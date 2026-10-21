"""The trust boundary: run Lean, and accept only a clean proof.

Generic over the Lake package, so a domain's library can live anywhere,
including outside this repository.

Accepted means all of: Lean exited cleanly, no error line, no `sorry`, and
`#print axioms` reports nothing beyond the permitted set. Attestations are
permitted by naming them, so a discharged judgement call is enumerable in the
certificate rather than invisible.
"""

from __future__ import annotations

import os
import pathlib
import re
import subprocess
from dataclasses import dataclass, field

# A generated case file is data plus one theorem. None of these belong in it,
# and each either runs code during elaboration (which can tamper with the
# environment `#print axioms` reads), weakens or skips the kernel, or reaches
# for compiled code. `set_option` is the important one: `debug.skipKernelTC`
# is an ordinary option that leaves no trace in the compiled module, so no
# downstream check could tell a skipped proof from a checked one.
FORBIDDEN = re.compile(
    r"\bset_option\b|skipKernelTC|#eval|#print\b|\brun_cmd\b|\brun_tac\b|"
    r"\brun_elab\b|\belab\b|\bmacro\b|\bsyntax\b|implemented_by|"
    r"@\[extern|\bnative_decide\b|\bunsafe\b|\bpartial\b|\baxiom\b|"
    r"\binitialize\b|\bopaque\b")


def forbidden(source: str) -> str | None:
    """The first forbidden construct outside string literals, or None.

    String literals are blanked first so an attribute value cannot trip the
    check — the snapshot is data and may contain anything, including text
    that happens to spell a Lean keyword.
    """
    code = re.sub(r'"(?:\\.|[^"\\])*"', '""', source)
    # «…» is a quoted identifier: whatever it spells, it is a name, never a
    # command, so a value that happens to read `elab` or `set_option` is data
    code = re.sub(r"«[^»\n]*»", "«»", code)
    match = FORBIDDEN.search(code)
    return match.group(0) if match else None


class BuildFailed(Exception):
    """The Lean package did not build, so nothing can be checked against it."""


#: Lean's own axioms. Anything else has to be allowed by name.
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


@dataclass(frozen=True)
class Check:
    theorem: str
    name: str
    statement: str
    proof: str
    accepted: bool
    axioms: tuple[str, ...]
    reason: str | None
    file: str
    #: the exact file checked, kept so a stored proof can be regenerated and
    #: compared byte for byte
    source: str = ""

    def as_dict(self) -> dict[str, object]:
        return {
            "theorem": self.theorem, "name": self.name,
            "statement": self.statement, "proof": self.proof,
            "accepted": self.accepted, "axioms": list(self.axioms),
            "reason": self.reason, "file": self.file,
        }


def case_source(namespace: str, imports, opens, defs: str, name: str,
                statement: str, proof: str) -> str:
    """The exact Lean file for one case.

    Deterministic, so the file stored beside a decision can be regenerated
    from the snapshot and compared byte for byte.
    """
    return (
        "".join(f"import {i}\n" for i in imports)
        + "".join(f"open {o}\n" for o in opens)
        + f"\nnamespace {namespace}\n{defs}\n"
        + f"theorem {name} : {statement} :=\n  {proof}\n\n"
        + f"end {namespace}\n"
        + f"#print axioms {namespace}.{name}\n"
    )


@dataclass
class Kernel:
    """Checks proofs against one Lake package."""

    package_dir: pathlib.Path
    case_dir: pathlib.Path | None = None
    allowed_axioms: frozenset[str] = STANDARD_AXIOMS
    timeout: float = 600.0
    #: every check made, for the certificate
    checks: list[Check] = field(default_factory=list)
    _built: bool = False

    def __post_init__(self) -> None:
        self.package_dir = pathlib.Path(self.package_dir).resolve()
        self.case_dir = pathlib.Path(
            self.case_dir or self.package_dir / "Cases").resolve()

    def build(self) -> None:
        """Build the package, once, before any proof is checked.

        `lake env lean <case>` neither rebuilds nor validates staleness, and
        Lean does not re-typecheck an imported `.olean`. So the whole
        hash-and-drift chain certified *source text* while the kernel ran
        whatever was last compiled: an olean built from a weakened rule, with
        the real rule restored on disk, produced a clean certificate citing
        the correct rule hash. Building here binds the two.
        """
        if self._built:
            return
        try:
            completed = subprocess.run(
                ["lake", "build"], cwd=self.package_dir, capture_output=True,
                text=True, timeout=self.timeout)
        except (subprocess.TimeoutExpired, OSError) as exc:
            raise BuildFailed(
                f"the Lean package build did not complete: "
                f"{type(exc).__name__}") from None
        if completed.returncode != 0:
            raise BuildFailed(
                "the Lean package does not build, so no proof can be checked "
                "against it:\n" + (completed.stdout + completed.stderr)[-500:])
        self._built = True

    def _shown(self, path: pathlib.Path) -> str:
        """The case file as reported. Falls back to the absolute path when the
        case directory sits outside the package, rather than raising from the
        error path and hiding the original failure."""
        try:
            return str(path.relative_to(self.package_dir))
        except ValueError:
            return str(path)

    def allow(self, *axioms: str) -> Kernel:
        """Permit named axioms — signed attestations discharging a judgement."""
        self.allowed_axioms = self.allowed_axioms | frozenset(axioms)
        return self

    def check(self, namespace: str, imports, opens, defs: str,
              name: str, statement: str, proof: str) -> Check:
        source = case_source(namespace, imports, opens, defs, name,
                             statement, proof)
        # `case_source` appends exactly one `#print axioms`; anything else
        # matching FORBIDDEN came from the caller's defs or proof.
        probe = source.replace(
            f"#print axioms {namespace}.{name}\n", "", 1)
        bad = forbidden(probe)
        if bad is not None:
            result = Check(
                theorem=f"{namespace}.{name}", name=name, statement=statement,
                proof=proof, accepted=False, axioms=(),
                reason=f"forbidden construct in case file: {bad!r}",
                file="", source=source)
            self.checks.append(result)
            return result
        try:
            self.build()             # the oleans the kernel will load
        except BuildFailed as exc:
            # fail closed: an unbuilt package has accepted nothing
            result = Check(
                theorem=f"{namespace}.{name}", name=name, statement=statement,
                proof=proof, accepted=False, axioms=(), reason=str(exc)[:160],
                file="", source=source)
            self.checks.append(result)
            return result
        path = self.case_dir / f"{namespace}_{name}.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)

        try:
            completed = subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=self.package_dir,
                capture_output=True, text=True, timeout=self.timeout,
                env={**os.environ},
            )
        except (subprocess.TimeoutExpired, OSError) as exc:
            # a kernel that did not finish has not accepted anything
            result = Check(
                theorem=f"{namespace}.{name}", name=name, statement=statement,
                proof=proof, accepted=False, axioms=(),
                reason=f"kernel check did not complete: {type(exc).__name__}",
                file=self._shown(path), source=source)
            self.checks.append(result)
            return result
        log = completed.stdout + completed.stderr

        # One axioms line, and it must be the one for *this* theorem. The
        # first version took `re.search(...)`, i.e. the first match — so a
        # `#print axioms` inside the interpolated defs masked the real
        # report and a locally declared `axiom` was accepted.
        axiom_lines = re.findall(
            r"'([\w.]+)' depends on axioms: \[(.*?)\]", log, re.S)
        want = f"{namespace}.{name}"
        own = [group for found, group in axiom_lines if found == want]
        if len(axiom_lines) > 1:
            used, masked = set(), True
        else:
            masked = False
            used = ({a.strip() for a in own[0].split(",") if a.strip()}
                    if own else
                    {a.strip() for _found, group in axiom_lines
                     for a in group.split(",") if a.strip()})

        # Lean prefixes every diagnostic with the absolute path, so a bare
        # `"error" in line` rejected any case whose directory contained the
        # word — and reported a warning as the error.
        error = next((line for line in log.splitlines()
                      if re.search(r":\s*error:", line)), None)
        has_sorry = ("declaration uses 'sorry'" in log or "sorryAx" in log)

        accepted = (completed.returncode == 0 and error is None
                    and not has_sorry and not masked
                    and used <= self.allowed_axioms)
        reason = None if accepted else (
            error.split("error:", 1)[-1].strip()[:160] if error
            else "uses sorry" if has_sorry
            else "more than one axioms report: the real one may be masked"
            if masked
            else f"disallowed axioms {sorted(used - self.allowed_axioms)}")

        result = Check(
            theorem=f"{namespace}.{name}", name=name, statement=statement,
            proof=proof, accepted=accepted, axioms=tuple(sorted(used)),
            reason=reason, file=self._shown(path), source=source,
        )
        self.checks.append(result)
        return result

    def check_source(self, source: str, path: pathlib.Path,
                     theorem: str) -> Check:
        """Check a stored proof file verbatim.

        `check` builds the case file from its parts; this takes one that was
        stored and re-runs it unchanged, which is what re-verifying a past
        decision means — the file is evidence, not a template.
        """
        # The stored theorem name is bare ("holds"); the file's line is
        # qualified ("#print axioms Case_abc.holds"). Matching on the name
        # missed, so the one `#print` every case file is supposed to carry
        # tripped the denylist and every recheck failed.
        probe = re.sub(r"^#print axioms [\w.]+\n?$", "", source,
                       count=1, flags=re.M)
        bad = forbidden(probe)
        if bad is not None:
            return Check(theorem=theorem, name=theorem, statement="",
                         proof="", accepted=False, axioms=(),
                         reason=f"forbidden construct in stored proof: {bad!r}",
                         file=str(path), source=source)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        try:
            completed = subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=self.package_dir,
                capture_output=True, text=True, timeout=self.timeout,
                env={**os.environ})
        except (subprocess.TimeoutExpired, OSError) as exc:
            return Check(theorem=theorem, name=theorem, statement="",
                         proof="", accepted=False, axioms=(),
                         reason=f"check did not complete: {type(exc).__name__}",
                         file=str(path), source=source)
        log = completed.stdout + completed.stderr
        lines = re.findall(r"'([\w.]+)' depends on axioms: \[(.*?)\]", log, re.S)
        used = ({a.strip() for _n, g in lines for a in g.split(",") if a.strip()}
                if len(lines) == 1 else set())
        error = next((l for l in log.splitlines()
                      if re.search(r":\s*error:", l)), None)
        sorry = "declaration uses 'sorry'" in log or "sorryAx" in log
        ok = (completed.returncode == 0 and error is None and not sorry
              and len(lines) == 1 and used <= self.allowed_axioms)
        reason = None if ok else (
            error.split("error:", 1)[-1].strip()[:160] if error
            else "uses sorry" if sorry
            else "no axioms report, or more than one"
            if len(lines) != 1
            else f"disallowed axioms {sorted(used - self.allowed_axioms)}")
        return Check(theorem=theorem, name=theorem, statement="", proof="",
                     accepted=ok, axioms=tuple(sorted(used)), reason=reason,
                     file=str(path), source=source)

    @staticmethod
    def version() -> str:
        try:
            return subprocess.run(
                ["lean", "--version"], capture_output=True, text=True,
                timeout=60).stdout.strip()
        except Exception as exc:                     # pragma: no cover
            return f"unavailable: {exc}"
