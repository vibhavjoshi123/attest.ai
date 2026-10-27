"""The Acceptor: fan out kernel checks without rebuilding or colliding.

Plan §2.4's concurrency rule, and its test: eight parallel `Acceptor.case`
calls with the same namespace and theorem name must write eight distinct
files, return correct outcomes, and cause exactly one `lake build`.

`lake` is replaced here, so these run offline and in milliseconds. What is
under test is the fingerprint and case-directory arithmetic, which is where
the hazard lives — the real toolchain is exercised by stage 13 of
`scripts/e2e.sh` and by `tests/test_lean_offline.py`.
"""

from __future__ import annotations

import pathlib
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from attest import kernel as kernel_mod                        # noqa: E402
from attest.domain import LeanPackage                           # noqa: E402
from attest.kernel import BuildFailed                           # noqa: E402
from attest.search.lean import (Acceptor, CaseRootInsidePackage,  # noqa: E402
                                Package, ScratchPackage)

NS, NAME = "Search.Attempt", "holds"
FAILURES: list[str] = []
RAN: list[str] = []
#: how many `check` calls a complete run makes. Asserted, because the count
#: is otherwise self-reported: an exception midway through a block skips the
#: checks after it, and a hardcoded total would still read "all passed".
EXPECTED = 31


def check(condition: bool, label: str) -> None:
    RAN.append(label)
    if not condition:
        FAILURES.append(label)


def check_raises(exc, label: str, fn) -> None:
    """One check either way, so a refusal counts as much as an acceptance."""
    try:
        fn()
    except exc:
        check(True, label)
    else:
        check(False, f"{label}: nothing was raised")


class FakeLake:
    """Counts `lake` invocations and answers them.

    Deliberately not a mock of the kernel: `Kernel.check` runs in full, so
    the axioms report, the error scan and the sorry scan are all the real
    ones reading this log.
    """

    def __init__(self, *, builds_ok: bool = True) -> None:
        self.builds_ok = builds_ok
        self.builds: list[pathlib.Path] = []
        self.runs: list[pathlib.Path] = []
        self.lock = threading.Lock()

    def __call__(self, argv, **kw):
        tail = argv[1:]
        with self.lock:
            if tail[:1] == ["build"]:
                self.builds.append(pathlib.Path(kw["cwd"]))
                code = 0 if self.builds_ok else 1
                return subprocess.CompletedProcess(
                    argv, code, "", "" if self.builds_ok else "boom")
            self.runs.append(pathlib.Path(tail[-1]))
        return subprocess.CompletedProcess(
            argv, 0, f"'{NS}.{NAME}' does not depend on any axioms\n", "")


def fake_package(root: pathlib.Path) -> Package:
    root.mkdir(parents=True, exist_ok=True)
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (root / "Search.lean").write_text("def one : Nat := 1\n")
    return Package.at(root)


def fake_domain(root: pathlib.Path) -> LeanPackage:
    """A package shaped like a domain's: a root module, a rule, a theorem,
    a `Cases/` directory that is not part of the library, and a `.lake`."""
    root.mkdir(parents=True, exist_ok=True)
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (root / "lakefile.lean").write_text("lean_lib Dom\n")
    (root / "Dom.lean").write_text(
        "import Dom.Schema\nimport Dom.Rules.R\nimport Dom.Properties\n")
    for name, text in (("Schema", "def s := 1"), ("Properties", "def p := 1")):
        (root / f"Dom/{name}.lean").parent.mkdir(parents=True, exist_ok=True)
        (root / f"Dom/{name}.lean").write_text(text + "\n")
    (root / "Dom/Rules").mkdir(parents=True, exist_ok=True)
    (root / "Dom/Rules/R.lean").write_text("def shipped := 1\n")
    (root / "Cases").mkdir(exist_ok=True)
    (root / "Cases/Case_old.lean").write_text("-- stale\n")
    (root / ".lake/build").mkdir(parents=True, exist_ok=True)
    (root / ".lake/build/leftover.lean").write_text("-- not a source\n")
    return LeanPackage(directory=root, root_module="Dom",
                       schema_namespace="Dom.Schema",
                       rules_namespace="Dom.Rules",
                       theorem_modules=("Dom.Properties",))


def one_case(acceptor: Acceptor, pkg: Package):
    return acceptor.case(pkg, NS, ["Search"], [], "", NAME, "True", "trivial")


def main() -> int:
    original = kernel_mod.subprocess.run
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        pkg = fake_package(tmp / "pkg")

        # 1. Eight parallel attempts: one build, eight distinct case files.
        lake = FakeLake()
        kernel_mod.subprocess.run = lake
        try:
            acceptor = Acceptor(tmp / "cases")
            with ThreadPoolExecutor(max_workers=8) as pool:
                results = list(pool.map(lambda _: one_case(acceptor, pkg),
                                        range(8)))
        finally:
            kernel_mod.subprocess.run = original

        check(len(lake.builds) == 1,
              f"8 parallel cases ran {len(lake.builds)} builds, not 1")
        check(acceptor.builds == {pathlib.Path(pkg.path): 1},
              f"the acceptor counted {acceptor.builds}")
        check(len(lake.runs) == 8,
              f"{len(lake.runs)} kernel runs for 8 cases")
        check(len(set(lake.runs)) == 8,
              f"8 cases wrote {len(set(lake.runs))} distinct files")
        check(all(r.accepted and r.outcome == "proved" for r in results),
              "a parallel case was not accepted: "
              + repr([(r.outcome, r.reason) for r in results
                      if not r.accepted][:1]))
        check(all(pkg.path not in path.parents for path in lake.runs),
              "a case file was written inside the package root")
        check(all(path.exists() for path in lake.runs),
              "a case file named in the log is not on disk")

        # 2. A case root inside the package is refused, not silently slow.
        #    Measured with the guard bypassed: 8 parallel cases then run 9
        #    builds instead of 1, each concurrently in the same `.lake`.
        inside = Acceptor(pkg.path / "Cases")
        check_raises(CaseRootInsidePackage,
                     "a case root inside the package is refused",
                     lambda: one_case(inside, pkg))

        # 3. Pre-marking does not disable the staleness check: a package that
        #    changed after the first build is rebuilt, which is the whole
        #    reason `_built_at` is a fingerprint and not a flag.
        lake = FakeLake()
        kernel_mod.subprocess.run = lake
        try:
            acceptor = Acceptor(tmp / "cases2")
            one_case(acceptor, pkg)
            (pkg.path / "Search.lean").write_text("def one : Nat := 2\n")
            one_case(acceptor, pkg)
        finally:
            kernel_mod.subprocess.run = original
        check(len(lake.builds) == 2,
              f"a changed package caused {len(lake.builds)} builds, not 2")

        # 4. A package that does not build accepts nothing, and says so as
        #    `not-run` rather than as a rejection of the proof.
        lake = FakeLake(builds_ok=False)
        kernel_mod.subprocess.run = lake
        try:
            result = one_case(Acceptor(tmp / "cases3"), pkg)
        finally:
            kernel_mod.subprocess.run = original
        check(not result.accepted and result.outcome == "not-run",
              f"a failed build gave {result.outcome!r}, not 'not-run'")
        check(not lake.runs, "the kernel ran against a package that failed")

        # 5. An explicit attempt_id is honoured, for a reproducible path.
        lake = FakeLake()
        kernel_mod.subprocess.run = lake
        try:
            Acceptor(tmp / "cases4").case(
                pkg, NS, ["Search"], [], "", NAME, "True", "trivial",
                attempt_id="pinned")
        finally:
            kernel_mod.subprocess.run = original
        check(lake.runs and lake.runs[0].parent.name == "pinned",
              f"attempt_id ignored: {lake.runs}")

        # -- ScratchPackage -------------------------------------------------
        dom = fake_domain(tmp / "dom")
        lake = FakeLake()
        kernel_mod.subprocess.run = lake
        try:
            scratch = ScratchPackage.build(
                dom, {"Dom.Rules.R": "def mutant := 2\n"}, tmp / "pkgs",
                drop=("Dom.Properties",))
            # 6. Built once, from a copy, never the domain package itself.
            check(len(lake.builds) == 1 and lake.builds[0] == scratch.path,
                  f"scratch built {lake.builds}, expected one in the copy")
            check(scratch.path != dom.directory,
                  "the scratch package is the domain package")
            check((dom.directory / "Dom/Rules/R.lean").read_text()
                  == "def shipped := 1\n",
                  "the domain's own rule module was overwritten")

            # 7. `extra` replaces, `drop` removes and strips its import.
            check((scratch.path / "Dom/Rules/R.lean").read_text()
                  == "def mutant := 2\n", "extra did not replace the module")
            check(not (scratch.path / "Dom/Properties.lean").exists(),
                  "a dropped module was copied anyway")
            root_text = (scratch.path / "Dom.lean").read_text()
            check("import Dom.Properties" not in root_text,
                  "the dropped module is still imported by the root module")
            check("import Dom.Schema" in root_text,
                  "stripping the dropped import removed a kept one")
            check((scratch.path / "lean-toolchain").exists()
                  and (scratch.path / "lakefile.lean").exists(),
                  "the toolchain pin or the lakefile was not copied")
            check(not (scratch.path / "Cases").exists(),
                  "the domain's stale case files were copied")
            check(not (scratch.path / ".lake").exists(),
                  ".lake was copied into the scratch package")

            # 8. `pkg.lean` matches the copy, so case files import what exists.
            check(scratch.lean is not None
                  and pathlib.Path(scratch.lean.directory) == scratch.path
                  and scratch.lean.theorem_modules == ()
                  and scratch.lean.rules_namespace == dom.rules_namespace,
                  f"pkg.lean does not match the copy: {scratch.lean}")

            # 9. Content-addressed: identical inputs reuse the build.
            again = ScratchPackage.build(
                dom, {"Dom.Rules.R": "def mutant := 2\n"}, tmp / "pkgs",
                drop=("Dom.Properties",))
            check(again.path == scratch.path and len(lake.builds) == 1,
                  f"an identical scratch package rebuilt: {lake.builds}")
            other = ScratchPackage.build(
                dom, {"Dom.Rules.R": "def mutant := 3\n"}, tmp / "pkgs",
                drop=("Dom.Properties",))
            check(other.path != scratch.path and len(lake.builds) == 2,
                  "a different mutant reused the first package's build")
        finally:
            kernel_mod.subprocess.run = original

        # 9b. An extra module the root module does not name is imported
        #     into it, or `lake build` succeeds without building it and the
        #     case file fails on a missing object file. Measured on the
        #     defect-2 mutants, whose rule ids differ from the shipped ones.
        lake = FakeLake()
        kernel_mod.subprocess.run = lake
        try:
            added = ScratchPackage.build(
                dom, {"Dom.Rules.Unlisted": "def extra := 1\n",
                      "Dom.Rules.R": "def mutant := 9\n"}, tmp / "pkgs")
        finally:
            kernel_mod.subprocess.run = original
        root_text = (added.path / "Dom.lean").read_text()
        check("import Dom.Rules.Unlisted" in root_text,
              "an unimported extra module was left out of the root module")
        check(root_text.count("import Dom.Rules.R\n") == 1,
              f"an already-imported module was imported twice:\n{root_text}")
        lines = [ln for ln in root_text.split("\n") if ln.strip()]
        check(all(ln.startswith("import ") for ln in lines),
              f"the added import landed after a non-import line:\n{root_text}")

        # 10. A module name that would escape the copy is refused.
        for bad in ("Dom/../../escape", "Dom.Rules/R"):
            check_raises(BuildFailed, f"module name {bad!r} is refused",
                         lambda bad=bad: ScratchPackage.build(
                             dom, {bad: "x"}, tmp / "pkgs"))

        # 11. No toolchain pin means no copy: an unpinned Lean may be one
        #     where the kernel admits False (CVE-2026-72844).
        unpinned = tmp / "unpinned"
        unpinned.mkdir()
        (unpinned / "lakefile.lean").write_text("lean_lib U\n")
        check_raises(BuildFailed, "a package with no toolchain pin is refused",
                     lambda: ScratchPackage.build(Package.at(unpinned), {},
                                                  tmp / "pkgs"))

    if len(RAN) != EXPECTED:
        FAILURES.append(f"{len(RAN)} checks ran, not {EXPECTED}: a block "
                        f"stopped early, so later checks never ran")
    for f in FAILURES:
        print("  FAIL", f)
    print(f"{len(RAN) - len(FAILURES)}/{EXPECTED} acceptor checks passed")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
