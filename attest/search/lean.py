"""Acceptance for the search: the only path from a candidate to "accepted".

Everything in `attest/search/` is untrusted. This module introduces no new
acceptance logic — `Acceptor.case` hands its parts to `kernel.Kernel.check`
unchanged and returns the `Check` that comes back. What it adds is the right
to *fan out*: many attempts against one package, in parallel, without the
three hazards map finding 6 names.

Two of those three are addressed here (plan §2.4):

*Parallel attempts overwriting each other.* `Kernel` writes its case file to
`{case_dir}/{namespace}_{name}.lean`. Attempts in a search share a namespace
and a theorem name — they differ in the snapshot — so a shared case directory
means eight workers writing one path. Each worker here gets a case directory
of its own, named for the attempt.

*A rebuild per attempt.* `Kernel.build` is cached on `_built_at`, a
fingerprint over the package's `.lean` files; `_fingerprint` skips `.lake` and
files directly in that kernel's *own* case directory, and nothing else. Case
directories inside the package root would therefore appear in every *other*
worker's fingerprint, so each would see a package that had changed under it
and run `lake build` — concurrently, in one `.lake`. So the case root must lie
outside the package root, and `case` refuses a root that does not.

Pre-marking a worker built does not disable the staleness check that
`_built_at` exists for: `check` calls `build`, which recomputes the
fingerprint and compares. A worker whose package changed since `prepare`
still builds. "Exactly one build" is a consequence of the package being
unchanged, not of the check being skipped.

`ScratchPackage`, `LeanSession` and `Feedback` (§2.4) are phase 0b, with the
comparator. They will expose the same `path` this module reads, so nothing
here changes when they land.
"""

from __future__ import annotations

import hashlib
import pathlib
import re
import threading
from dataclasses import dataclass

from attest.kernel import STANDARD_AXIOMS, BuildFailed, Check, Kernel


@dataclass(frozen=True)
class Package:
    """A built Lake package the search checks against.

    Slice A checks against a domain's own package, read-only: no search code
    writes into it. `ScratchPackage` will be a copy plus extra modules, with
    this same `path`.
    """

    path: pathlib.Path

    @classmethod
    def at(cls, directory) -> Package:
        return cls(pathlib.Path(directory).resolve())


_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")

#: directories under a package root that are not part of its library
_NOT_SOURCE = ("Cases",)


@dataclass(frozen=True)
class ScratchPackage:
    """A content-addressed copy of a domain's Lake package, plus modules.

    Never the domain package itself. The search compiles rules that are
    deliberately wrong — a mutant, a candidate formalization — and writing
    one into a domain package would leave a domain whose compiled rule is not
    what its `.rule` file says. It would also change that package's
    fingerprint under every other reader.

    The copy is why a mutant's verdict can be confirmed at all. A case file
    binds its statement to the compiled rule with `Iff.rfl`, so a case about
    a mutant checked against the shipped package is *refuted* — correctly:
    the mutant's reading is not the shipped rule's. Confirming what the
    mutant says needs a package in which the mutant is the rule.

    `path` is named for a hash of everything that went into it, so a repeated
    confirmation reuses the build instead of paying for it again.

    Phase 0b replaces the copied lakefile with one of its own, because the
    comparator needs `Challenge` and `Solution` libraries that a domain's
    single `lean_lib` does not declare. Everything else here stays.
    """

    path: pathlib.Path
    #: the `LeanPackage` that matches this copy: same namespaces, this
    #: directory, and only the theorem modules that survived `drop`. Case
    #: files must be generated from THIS, not from the domain's own package
    #: — `runner.case_file` imports every theorem module it is given, and
    #: importing a module the copy does not have fails the check with a
    #: missing object file rather than anything about the proof.
    lean: object = None

    @classmethod
    def build(cls, lean, extra: dict[str, str], root, *,
              drop: tuple[str, ...] = ()) -> ScratchPackage:
        """Copy `lean`'s package, write `extra` modules over it, build once.

        `extra` maps a module name to its source. A name is validated before
        it becomes a path: `Rules/../../x` would otherwise write outside the
        copy, and in a search the names come from whatever proposed them.

        `drop` names modules to leave out, with their import lines stripped
        from every module that remains. Theorem modules need it: they prove
        properties *of* the shipped rules, so a copy holding a mutant cannot
        build with them — measured on fixture, where the historical
        same-day-tie mutant leaves `Properties.band_exclusive` at
        `sorryAx` and the whole package therefore fails. That failure is
        corroboration, not an obstacle: the proof system rejects the mutant
        for the same reason the search flagged it.

        Dropping them cannot make a false verdict provable. A case file binds
        its statement to the compiled rule with `Iff.rfl`, and the dropped
        modules are proofs *about* a rule, never part of what a verdict
        means. What is lost is only the package's own guarantee that its
        rules satisfy their properties — which is exactly what a mutant is
        built to violate.
        """
        import dataclasses
        import hashlib
        import shutil

        source = package_root(lean)
        root = pathlib.Path(root).resolve()
        files: dict[str, str] = {}
        for name in ("lakefile.lean", "lean-toolchain", "lake-manifest.json"):
            here = source / name
            if here.exists():
                files[name] = here.read_text()
        if "lean-toolchain" not in files:
            raise BuildFailed(
                f"{source} has no lean-toolchain, so a copy would be checked "
                f"by whatever Lean elan happens to default to")
        for path in sorted(source.rglob("*.lean")):
            parts = path.relative_to(source).parts
            if ".lake" in parts or parts[0] in _NOT_SOURCE:
                continue
            files[str(path.relative_to(source))] = path.read_text()
        for name, text in sorted(extra.items()):
            if not _MODULE.match(name):
                raise BuildFailed(f"invalid module name {name!r}")
            files[str(pathlib.Path(*name.split("."))) + ".lean"] = text
        for name in drop:
            if not _MODULE.match(name):
                raise BuildFailed(f"invalid module name {name!r}")
            files.pop(str(pathlib.Path(*name.split("."))) + ".lean", None)
        if drop:
            gone = {f"import {name}" for name in drop}
            files = {
                path: "\n".join(line for line in text.split("\n")
                                 if line.strip() not in gone)
                for path, text in files.items()}

        # An extra module nothing imports is never built, and `lake build`
        # succeeds without it. The case file then imports a module with no
        # object file and the check comes back refuted citing a missing
        # `.olean` — which reads as a verdict about the proof. Measured on
        # the defect-2 mutants, whose rule ids differ from the shipped ones
        # (`fixture.latest-high-factid`), so they compile to modules the
        # domain's root module does not name.
        root_module = getattr(lean, "root_module", None)
        root_file = f"{root_module}.lean" if root_module else None
        if root_file in files:
            text = files[root_file]
            present = {ln.strip() for ln in text.split("\n")}
            missing = [f"import {name}" for name in sorted(extra)
                       if f"import {name}" not in present]
            if missing:
                lines = text.split("\n")
                last = max((i for i, ln in enumerate(lines)
                            if ln.strip().startswith("import ")), default=-1)
                lines[last + 1:last + 1] = missing
                files[root_file] = "\n".join(lines)

        digest = hashlib.sha256()
        for name, text in sorted(files.items()):
            digest.update(name.encode())
            digest.update(b"\x00")
            digest.update(text.encode())
            digest.update(b"\x00")
        where = root / f"scratch-{digest.hexdigest()[:16]}"
        kept = tuple(m for m in getattr(lean, "theorem_modules", ())
                     if m not in drop)
        adjusted = (dataclasses.replace(lean, directory=where,
                                        theorem_modules=kept)
                    if dataclasses.is_dataclass(lean) else None)
        ready = where / ".attest-built"
        if ready.exists():
            return cls(where, adjusted)

        if where.exists():
            shutil.rmtree(where)
        for name, text in files.items():
            out = where / name
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text)
        Kernel(where).build()             # raises BuildFailed, leaving no marker
        ready.write_text(str(source) + "\n")
        return cls(where, adjusted)


def package_root(pkg) -> pathlib.Path:
    """The package root of a `Package`, a `LeanPackage`, or a path."""
    for attr in ("path", "directory"):
        inner = getattr(pkg, attr, None)
        if inner is not None:
            return pathlib.Path(inner).resolve()
    return pathlib.Path(pkg).resolve()


@dataclass(frozen=True)
class Bound:
    """One package's Acceptor, wearing `Kernel.check`'s signature.

    `runner.CaseFile.check` calls `kernel.check(namespace, ...)`. Binding the
    package here lets the search hand an Acceptor to anything that expected a
    Kernel, without `runner` — core, trusted — learning that the search
    exists.
    """

    acceptor: Acceptor
    pkg: object

    def check(self, namespace: str, imports, opens, defs: str, name: str,
              statement: str, proof: str) -> Check:
        return self.acceptor.case(self.pkg, namespace, imports, opens, defs,
                                  name, statement, proof)


class CaseRootInsidePackage(Exception):
    """The case root is inside the package root, so workers would rebuild."""


class Acceptor:
    """Kernel acceptance in a fresh process, safe to fan out.

    Build once, then fan out. `prepare` runs `lake build` a single time per
    package and keeps the fingerprint it built at; each `case` call gives its
    worker that fingerprint and a case directory of its own.
    """

    def __init__(self, case_root, *,
                 allowed_axioms: frozenset[str] = STANDARD_AXIOMS,
                 timeout: float = 600.0) -> None:
        self.case_root = pathlib.Path(case_root).resolve()
        self.allowed_axioms = allowed_axioms
        self.timeout = timeout
        #: how many times this Acceptor has run `lake build`, per package.
        #: Read by the concurrency test; not otherwise part of the interface.
        self.builds: dict[pathlib.Path, int] = {}
        self._built: dict[pathlib.Path, str] = {}
        self._attempts = 0
        self._lock = threading.Lock()

    # -- package preparation -------------------------------------------------

    def _check_outside(self, root: pathlib.Path) -> None:
        if self.case_root == root or root in self.case_root.parents:
            raise CaseRootInsidePackage(
                f"the case root {self.case_root} is inside the package "
                f"{root}: every worker's fingerprint would change as the "
                f"others wrote their cases, and each would run `lake build`")

    def prepare(self, pkg) -> str:
        """Build the package if it is not already built at its current source.

        Returns the fingerprint to mark workers with. Raises `BuildFailed`
        if the package does not build, so no worker is marked built against a
        package that has accepted nothing.
        """
        root = package_root(pkg)
        self._check_outside(root)
        probe = Kernel(root, case_dir=self.case_root / "_fingerprint",
                       timeout=self.timeout)
        with self._lock:
            now = probe._fingerprint()
            if self._built.get(root) == now:
                return now
            probe.build()
            self._built[root] = probe._built_at
            self.builds[root] = self.builds.get(root, 0) + 1
            return probe._built_at

    # -- acceptance ----------------------------------------------------------

    def _attempt_id(self, namespace: str, name: str, statement: str,
                    proof: str) -> str:
        """A directory name unique to this attempt.

        The content hash alone is not enough: a search re-checks the same
        statement against different snapshots, and the concurrency test runs
        eight calls with identical arguments. A counter makes the directory
        distinct even then, which is the point of giving each worker one.
        """
        digest = hashlib.sha256(
            "\x00".join((namespace, name, statement, proof)).encode()
        ).hexdigest()[:12]
        with self._lock:
            self._attempts += 1
            return f"{namespace}_{name}-{digest}-{self._attempts:05d}"

    def case(self, pkg, namespace: str, imports, opens, defs: str,
             name: str, statement: str, proof: str, *,
             attempt_id: str | None = None) -> Check:
        """Check one case file. The only path to an accepted search result.

        Pass `attempt_id` to make the case path reproducible across runs;
        it must be unique among attempts running at the same time.
        """
        root = package_root(pkg)
        try:
            fingerprint = self.prepare(pkg)
        except BuildFailed:
            # Fail closed, and in one place. `Kernel.check` already turns a
            # failed build into a `not-run` Check with the build log in it;
            # building that Check here instead would put the shape of a
            # kernel outcome in untrusted code. So leave the worker unmarked
            # and let it try: it fails the same way, and reports it the same
            # way. The repeated build only costs anything on a package that
            # does not build, where the search is over regardless.
            fingerprint = None
        attempt = attempt_id or self._attempt_id(namespace, name, statement,
                                                 proof)
        worker = Kernel(root, case_dir=self.case_root / attempt,
                        allowed_axioms=self.allowed_axioms,
                        timeout=self.timeout)
        worker._built_at = fingerprint
        return worker.check(namespace, imports, opens, defs, name, statement,
                            proof)

    def bind(self, pkg) -> Bound:
        """This Acceptor as a stand-in for a `Kernel` on one package."""
        return Bound(self, pkg)
