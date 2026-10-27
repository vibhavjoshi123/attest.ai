"""The Acceptor against real Lean: fan-out, and a mutant kernel-confirmed.

`test_acceptor.py` replaces `lake` and checks the fingerprint and
case-directory arithmetic offline. This runs the same paths on the real
toolchain, because the hazard it guards against — eight workers rebuilding
one `.lake` concurrently — only exists with a real build.

It also closes the loop cx-0 needs: a historical fixture defect, found by
the search, kernel-confirmed with standard axioms. That cannot be done
against the shipped package, where the `Iff.rfl` binding correctly refutes a
mutant's verdict, so it goes through a `ScratchPackage` in which the mutant
IS the rule.
"""

from __future__ import annotations

import pathlib
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tests"),
                str(ROOT / "tests" / "fixtures")]

from attest import rulec                                        # noqa: E402
from attest.kernel import STANDARD_AXIOMS                       # noqa: E402
from attest.props import parse_family, validate                 # noqa: E402
from attest.search.cx import search as cx                       # noqa: E402
from attest.search.lean import (Acceptor, Package,              # noqa: E402
                                ScratchPackage)

import schema_offline                                           # noqa: E402

RULES = ROOT / "tests" / "fixtures" / "rules"
MUTANTS = ROOT / "tests" / "mutants" / "fixture"
LEAN_DIR = ROOT / "tests" / "fixtures" / "lean"
BAND = ("latest-high", "latest-low")

FAILURES: list[str] = []
RAN: list[str] = []
EXPECTED = 9


def check(condition: bool, label: str) -> None:
    RAN.append(label)
    if not condition:
        FAILURES.append(label)


def fixture_lean():
    from attest.domain import LeanPackage
    return LeanPackage(directory=LEAN_DIR, root_module="Fixture",
                       schema_namespace="Fixture.Schema",
                       rules_namespace="Fixture.Rules",
                       theorem_modules=("Fixture.Properties",))


def main() -> int:
    model = schema_offline.model(ROOT / "tests" / "fixtures" / "schema.tql")
    lean = fixture_lean()
    pkg = Package.at(LEAN_DIR)

    with tempfile.TemporaryDirectory(prefix="attest-acceptor-") as tmp:
        tmp = pathlib.Path(tmp)

        # 1. Eight real parallel checks: one build, eight files, all proved.
        acceptor = Acceptor(tmp / "cases")
        started = time.time()
        with ThreadPoolExecutor(max_workers=8) as pool:
            results = list(pool.map(
                lambda _: acceptor.case(pkg, "Fixture.Probe", ["Fixture"],
                                        [], "", "holds", "(1:Nat) + 1 = 2",
                                        "by decide"),
                range(8)))
        elapsed = time.time() - started
        builds = sum(acceptor.builds.values())
        check(builds == 1, f"8 parallel real checks ran {builds} builds, not 1")
        check(all(r.accepted for r in results),
              "a parallel real check was not accepted: "
              + repr([(r.outcome, r.reason) for r in results
                      if not r.accepted][:1]))
        dirs = {pathlib.Path(r.file).parent for r in results}
        check(len(dirs) == 8, f"8 parallel checks shared {len(dirs)} case dirs")
        check(all(LEAN_DIR not in d.parents for d in dirs),
              "a real case file was written inside the domain package")
        print(f"  8 parallel real checks in {elapsed:.1f}s, {builds} build")

        # 2. The same path refutes a false statement, so acceptance above is
        #    not the path saying yes to everything.
        false = acceptor.case(pkg, "Fixture.Probe", ["Fixture"], [], "",
                              "nope", "(1:Nat) = 2", "by decide")
        check(not false.accepted and false.outcome == "refuted",
              f"a false statement came back {false.outcome!r}")

        # 3. A historical defect, found and then kernel-confirmed.
        decls = [d for f in RULES.glob("*.family")
                 for d in parse_family(f.read_text())]
        validate(decls, {p.stem for p in RULES.glob("*.rule")})
        decl = next(d for d in decls
                    if d.id == "fixture.alpha-band.exclusive")
        rules = {n: rulec.load(str(MUTANTS / f"historical-{n}.rule"))
                 for n in BAND}
        found = cx.search(decl, rules, model, max_rows=2, limit=4000,
                          stop_after=1)
        check(bool(found), "the historical same-day tie was not rediscovered")
        if found:
            extra = {rulec.module(r, lean.rules_namespace):
                     rulec.compile_lean(r, model, lean.rules_namespace,
                                        lean.schema_namespace)
                     for r in rules.values()}
            scratch = ScratchPackage.build(lean, extra, tmp / "pkgs",
                                           drop=lean.theorem_modules)
            confirmer = Acceptor(tmp / "mutcases")
            report = cx.confirm(found[0], rules, model, scratch.lean,
                                confirmer.bind(scratch))
            verdicts = {k: v for k, v in report.items()
                        if not k.startswith("_")}
            check(report["_confirmed"],
                  "the violation was not kernel-confirmed: "
                  + repr({k: (v["outcome"], v["reason"])
                          for k, v in verdicts.items()})
                  + " unchecked: " + repr(report.get("_unchecked")))
            check(all(set(v["axioms"]) <= set(STANDARD_AXIOMS)
                      for v in verdicts.values()),
                  f"confirmed with non-standard axioms: "
                  f"{[v['axioms'] for v in verdicts.values()]}")
            print(f"  defect confirmed on {len(verdicts)} rules, axioms "
                  f"{sorted({a for v in verdicts.values() for a in v['axioms']})}")

            # 4. The copy is content-addressed, so a second search reuses it.
            before = sum(confirmer.builds.values())
            again = ScratchPackage.build(lean, extra, tmp / "pkgs",
                                         drop=lean.theorem_modules)
            check(again.path == scratch.path,
                  "an identical scratch package was rebuilt elsewhere")
            print(f"  scratch package reused ({before} build for the mutant)")

    if len(RAN) != EXPECTED:
        FAILURES.append(f"{len(RAN)} checks ran, not {EXPECTED}")
    for f in FAILURES:
        print("  FAIL", f)
    print(f"{len(RAN) - len(FAILURES)}/{EXPECTED} live acceptor checks passed")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
