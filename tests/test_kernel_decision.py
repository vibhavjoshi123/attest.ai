"""The one predicate everything else rests on: did Lean accept this proof?

`Kernel.check` reads a Lean log and returns a verdict. Every attestation,
every certificate and every `recheck` is that verdict carried forward, so a
log this function misreads is a decision the system claims Lean approved
when it did not.

It had no test of its own. `tests/test_acceptor.py` drives it through a fake
`lake`, but that fake answers every invocation with the same clean
"does not depend on any axioms", so only the accepting branch ever ran. The
refusing branches — the masked report, the path-prefixed error, the timeout
that must not read as a rejection — were reachable only through
`tests/test_lean_offline.py`, which needs a real Lean and takes 73 seconds.
A trust boundary tested only by the slowest suite in the tree is a trust
boundary that gets tested last, or not at all.

So: real `Kernel.check`, in full, over scripted logs. The logs are the ones
Lean actually emits, including the two spellings of an axioms report and the
absolute path it prefixes to every diagnostic. Nothing here is mocked except
the subprocess — the axiom parse, the error scan, the sorry scan and the
acceptance arithmetic are the shipped ones.

    python3 tests/test_kernel_decision.py
"""

from __future__ import annotations

import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from attest import kernel as kernel_mod                          # noqa: E402
from attest.kernel import (STANDARD_AXIOMS, Kernel,              # noqa: E402
                           case_source)

NS, NAME = "Cases", "holds"
THM = f"{NS}.{NAME}"

FAILURES: list[str] = []
RAN: list[str] = []
#: how many checks a complete run makes. Asserted at the end: an exception
#: part way through skips everything after it, and a self-reported total
#: would still print "all passed".
EXPECTED = 81


def check(condition: bool, label: str) -> None:
    RAN.append(label)
    if not condition:
        FAILURES.append(label)


class ScriptedLake:
    """Answers `lake build` and `lake env lean` with a scripted result.

    `Kernel.check` runs in full against it: what is under test is what the
    kernel concludes from a log, so the log is the only thing supplied.
    """

    def __init__(self, stdout: str = "", stderr: str = "", code: int = 0, *,
                 builds_ok: bool = True, raises: Exception | None = None):
        self.stdout, self.stderr, self.code = stdout, stderr, code
        self.builds_ok, self.raises = builds_ok, raises
        self.builds, self.lean_runs = 0, 0

    def __call__(self, argv, **kw):
        if argv[1:2] == ["build"]:
            self.builds += 1
            return subprocess.CompletedProcess(
                argv, 0 if self.builds_ok else 1, "",
                "" if self.builds_ok else "unknown identifier 'foo'")
        self.lean_runs += 1
        if self.raises is not None:
            raise self.raises
        return subprocess.CompletedProcess(argv, self.code, self.stdout,
                                           self.stderr)


def axioms_line(theorem: str, *axioms: str) -> str:
    """Lean's own wording, in both of its spellings."""
    if not axioms:
        return f"'{theorem}' does not depend on any axioms\n"
    return f"'{theorem}' depends on axioms: [{', '.join(axioms)}]\n"


def package(root: pathlib.Path) -> pathlib.Path:
    root.mkdir(parents=True, exist_ok=True)
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (root / "lakefile.lean").write_text("lean_lib Dom\n")
    (root / "Dom.lean").write_text("def one : Nat := 1\n")
    return root


def verdict(tmp: pathlib.Path, lake: ScriptedLake, *, kernel: Kernel = None,
            defs: str = "", proof: str = "trivial", cases: str = "Cases"):
    """One `check` against a scripted log. Returns (Check, lake)."""
    original = kernel_mod.subprocess.run
    kernel_mod.subprocess.run = lake
    try:
        k = kernel or Kernel(package(tmp / "pkg"), case_dir=tmp / cases)
        return k.check(NS, ["Dom"], [], defs, NAME, "True", proof), k
    finally:
        kernel_mod.subprocess.run = original


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)

        # ─── 1. What the kernel must accept ──────────────────────────────
        # Lean's two spellings of a clean report, and the standard axioms
        # named one at a time: `used <= allowed` is a subset test, and a
        # subset test written as equality would refuse every proof that
        # happens to use only one of the three.
        for label, used in (("no axioms at all", ()),
                            ("propext alone", ("propext",)),
                            ("choice alone", ("Classical.choice",)),
                            ("all three standard axioms",
                             tuple(sorted(STANDARD_AXIOMS)))):
            got, _ = verdict(tmp, ScriptedLake(axioms_line(THM, *used)))
            check(got.accepted and got.outcome == "proved",
                  f"a proof depending on {label} is accepted")
            check(got.axioms == tuple(sorted(used)),
                  f"the axioms of {label} are recorded, sorted")
            check(got.reason is None,
                  f"an accepted proof of {label} carries no reason")

        # A warning is not an error. Lean warns about unused variables in
        # generated rule modules constantly; refusing on "warning" would
        # make the whole system unusable, and scanning for the bare word
        # "error" refuses on the path, not the diagnostic.
        warned = ("/Users/x/pkg/Cases/Cases_holds.lean:3:7: warning: unused "
                  "variable `h`\n" + axioms_line(THM, "propext"))
        got, _ = verdict(tmp, ScriptedLake(warned))
        check(got.accepted, "a warning in the log is not an error")

        # The historical defect, pinned: `"error" in line` refused any case
        # whose DIRECTORY spelled the word.
        here = tmp / "error-cases"
        got, _ = verdict(tmp, ScriptedLake(
            f"{here}/Cases_holds.lean:1:1: warning: unused\n"
            + axioms_line(THM, "propext")), cases="error-cases")
        check(got.accepted,
              "a case directory named 'error-cases' is still accepted")

        # ─── 2. What the kernel must refuse ──────────────────────────────
        # A disallowed axiom, named so the reader knows which.
        got, _ = verdict(tmp, ScriptedLake(
            axioms_line(THM, "propext", "myAxiom")))
        check(not got.accepted and got.outcome == "refuted",
              "an unlisted axiom is refuted")
        check("myAxiom" in (got.reason or ""),
              "the refusal names the axiom that was not allowed")
        check(got.axioms == ("myAxiom", "propext"),
              "the axioms are recorded even when refused")

        # sorryAx reported as an axiom. It is not in the standard set, so
        # the subset test alone catches it — checked because `sorry` is the
        # one-character hole through the whole system.
        got, _ = verdict(tmp, ScriptedLake(axioms_line(THM, "sorryAx")))
        check(not got.accepted, "sorryAx as a reported axiom is refuted")

        # ...and Lean's other way of saying it, which names no axiom at all.
        got, _ = verdict(tmp, ScriptedLake(
            "Cases_holds.lean:4:2: warning: declaration uses 'sorry'\n"
            + axioms_line(THM, "propext")))
        check(not got.accepted, "'declaration uses sorry' is refuted")
        check("sorry" in (got.reason or ""), "the refusal says it was sorry")

        # An error, with the absolute path Lean prefixes to it.
        got, _ = verdict(tmp, ScriptedLake(
            "/Users/x/pkg/Cases/Cases_holds.lean:5:0: error: unknown "
            "identifier 'foo'\n", code=1))
        check(not got.accepted and got.outcome == "refuted",
              "a path-prefixed error is refuted")
        check("unknown identifier" in (got.reason or ""),
              "the refusal quotes the error, not the path")

        # Lean exited non-zero and said nothing a scan recognises. Fail
        # closed: the kernel cannot read this, so it has not accepted it.
        got, _ = verdict(tmp, ScriptedLake("", "killed", code=137))
        check(not got.accepted,
              "a non-zero exit with no readable diagnostic is refuted")

        # ─── 3. The masked report: the defect this arithmetic exists for ──
        # A `#print axioms` inside the caller's defs prints FIRST, so
        # `re.search` read someone else's report and a locally declared
        # axiom was accepted. The rule is: exactly one report, and it must
        # be this theorem's.
        masked = (axioms_line("Dom.helper")                 # not ours
                  + axioms_line(THM, "propext"))            # ours, second
        got, _ = verdict(tmp, ScriptedLake(masked))
        check(not got.accepted, "two reports: the real one may be masked")
        check("masked" in (got.reason or "").lower()
              or "exactly one" in (got.reason or ""),
              "the refusal says the report could not be trusted")

        # Zero reports used to read as "no axioms used", which is also what
        # a suppressed report looks like.
        got, _ = verdict(tmp, ScriptedLake("built successfully\n"))
        check(not got.accepted, "no axioms report at all is refuted")

        # One report, for the wrong theorem.
        got, _ = verdict(tmp, ScriptedLake(axioms_line("Dom.somethingElse")))
        check(not got.accepted,
              "a report about another theorem is not this theorem's")

        # Our report plus a duplicate of it: still not exactly one.
        got, _ = verdict(tmp, ScriptedLake(
            axioms_line(THM, "propext") + axioms_line(THM, "propext")))
        check(not got.accepted, "the same report twice is refused")

        # ─── 4. Did not finish ≠ rejected ────────────────────────────────
        # A timeout reported as a rejection becomes a recorded disagreement
        # between Lean and TypeDB that never happened.
        for label, exc in (
                ("a timeout", subprocess.TimeoutExpired("lake", 1)),
                ("lean not on PATH", OSError("No such file"))):
            got, _ = verdict(tmp, ScriptedLake(raises=exc))
            check(got.outcome == "not-run" and not got.accepted,
                  f"{label} is not-run, not refuted")
            check(not got.ran, f"{label} says nothing about the proof")

        # A package that does not build has checked nothing — and Lean must
        # not be invoked at all, since it would read stale oleans.
        lake = ScriptedLake(axioms_line(THM), builds_ok=False)
        got, _ = verdict(tmp, lake)
        check(got.outcome == "not-run" and not got.accepted,
              "a failed build is not-run")
        check(lake.lean_runs == 0, "no proof is checked against an unbuilt "
                                   "package")

        # ─── 5. Refused before Lean saw it ───────────────────────────────
        # The denylist runs on the generated file, so a forbidden construct
        # in the caller's defs or proof must stop the check dead. If Lean
        # ran, `set_option debug.skipKernelTC true` would have run with it.
        for label, kw in (
                ("set_option in the defs",
                 {"defs": "set_option debug.skipKernelTC true\n"}),
                ("native_decide as the proof", {"proof": "by native_decide"}),
                ("a locally declared axiom in the defs",
                 {"defs": "axiom cheat : False\n"})):
            lake = ScriptedLake(axioms_line(THM))
            got, _ = verdict(tmp, lake, **kw)
            check(got.outcome == "refused" and not got.accepted,
                  f"{label} is refused")
            check(lake.lean_runs == 0 and lake.builds == 0,
                  f"{label} never reached Lean")
            check(got.file == "", f"{label} wrote no case file")

        # The `#print axioms` the kernel appends itself is not a forbidden
        # `#print` — otherwise nothing would ever be checked. This is the
        # one exemption, and it is exactly one.
        got, _ = verdict(tmp, ScriptedLake(axioms_line(THM)))
        check(got.accepted,
              "the kernel's own #print axioms is not read as forbidden")

        # ─── 6. The record it leaves ─────────────────────────────────────
        lake = ScriptedLake(axioms_line(THM, "propext"))
        kernel = Kernel(package(tmp / "pkg"), case_dir=tmp / "rec")
        got, kernel = verdict(tmp, lake, kernel=kernel)
        check(kernel.checks == [got], "the check is recorded, exactly once")
        check(got.theorem == THM and got.name == NAME,
              "the record names the theorem that was checked")
        check(f"#print axioms {THM}" in got.source,
              "the record carries the exact file that was checked")
        check((tmp / "rec" / f"{NS}_{NAME}.lean").read_text() == got.source,
              "the file on disk is the file in the record")

        # Every outcome is one of the four, and `accepted` agrees with it.
        # `Check.__post_init__` enforces this, so a verdict that contradicts
        # itself cannot be constructed — checked here because the rest of
        # this file reads `outcome` and `accepted` as interchangeable.
        seen = set()
        for lake in (ScriptedLake(axioms_line(THM)),
                     ScriptedLake("", "e", code=1),
                     ScriptedLake("", builds_ok=False),
                     ScriptedLake(axioms_line(THM))):
            got, _ = verdict(tmp, lake)
            seen.add(got.outcome)
            check((got.outcome == "proved") == got.accepted,
                  f"outcome {got.outcome!r} agrees with accepted")
        got, _ = verdict(tmp, ScriptedLake(axioms_line(THM)),
                         proof="by native_decide")
        seen.add(got.outcome)
        check(seen == {"proved", "refuted", "not-run", "refused"},
              f"only {sorted(seen)} of the four outcomes were produced")

        # ─── 7. allow() widens the set, by name, and only by name ────────
        # A signed attestation discharges a judgement no proof can reach.
        # It must be admissible, and nothing else must ride in with it.
        signed = Kernel(package(tmp / "pkg"),
                        case_dir=tmp / "signed").allow("att_reviewer_signed")
        got, _ = verdict(tmp, ScriptedLake(
            axioms_line(THM, "att_reviewer_signed", "propext")),
            kernel=signed)
        check(got.accepted, "a named attestation axiom is admissible")
        got, _ = verdict(tmp, ScriptedLake(
            axioms_line(THM, "att_someone_else")), kernel=signed)
        check(not got.accepted,
              "allowing one attestation does not allow another")
        check("propext" in STANDARD_AXIOMS
              and "sorryAx" not in STANDARD_AXIOMS,
              "the standard set is Lean's three, and not sorryAx")

        # ─── 8. The same question asked of a STORED proof ────────────────
        # `check_source` is the re-verification path: `recheck` hands it a
        # file read back out of the store and asks whether it still checks.
        # It carries its OWN copy of the acceptance arithmetic — a second
        # implementation of the most trust-critical predicate in the system
        # — and until this block it was exercised only by the live scenario
        # suite, which needs a TypeDB server. Two implementations of one
        # predicate, one of them tested only when a database is reachable,
        # is how they drift: the comment in `check_source` records that it
        # once accepted a clean report belonging to a DIFFERENT theorem,
        # because `check` gained that check and this path did not.
        #
        # The file is evidence, not a template, so what it may contain is
        # not up to Attest — a stored snapshot can say anything.
        stored = case_source("Case_abc", ["Dom"], [], "", NAME, "True",
                             "trivial")
        QUAL = f"Case_abc.{NAME}"

        def recheck(lake, source=None, qualified=None, kernel=None):
            original = kernel_mod.subprocess.run
            kernel_mod.subprocess.run = lake
            try:
                k = kernel or Kernel(package(tmp / "pkg"),
                                     case_dir=tmp / "rc")
                return k.check_source(source or stored,
                                      tmp / "rc" / "Case_abc.lean",
                                      NAME, qualified=qualified)
            finally:
                kernel_mod.subprocess.run = original

        # The bare stored name is "holds"; the file's report is qualified.
        # Matching on the bare name alone once missed, and every recheck
        # failed — so both spellings are checked here.
        got = recheck(ScriptedLake(axioms_line(QUAL, "propext")))
        check(got.accepted and got.outcome == "proved",
              "a stored proof with a clean qualified report is accepted")
        got = recheck(ScriptedLake(axioms_line(QUAL, "propext")),
                      qualified=QUAL)
        check(got.accepted,
              "the same, with the qualified name the runner passes")

        # The defect the comment names: a stored file carrying someone
        # else's clean report, accepted on behalf of a theorem whose axioms
        # were never read.
        got = recheck(ScriptedLake(axioms_line("Other.trivial")),
                      qualified=QUAL)
        check(not got.accepted,
              "a report naming another theorem is not this proof's")
        check("names" in (got.reason or ""),
              "the refusal says which theorem the report was about")
        got = recheck(ScriptedLake(axioms_line("Other.trivial")))
        check(not got.accepted,
              "...and the same with no qualified name to compare against")

        # A report whose bare name merely ENDS the same way is not enough
        # when the runner said which theorem it wants.
        got = recheck(ScriptedLake(axioms_line(f"Somewhere.{NAME}")),
                      qualified=QUAL)
        check(not got.accepted,
              "a qualified name must match, not merely end alike")

        for label, log, why in (
                ("two reports",
                 axioms_line(QUAL) + axioms_line(QUAL), "more than one"),
                ("no report at all", "built\n", "none"),
                ("sorry",
                 "Case_abc.lean:4:2: warning: declaration uses 'sorry'\n"
                 + axioms_line(QUAL), "sorry"),
                ("a disallowed axiom",
                 axioms_line(QUAL, "myAxiom"), "an unlisted axiom")):
            got = recheck(ScriptedLake(log), qualified=QUAL)
            check(not got.accepted, f"a stored proof with {label} is refused")
            check(got.reason is not None,
                  f"the refusal of {label} says why ({why})")

        got = recheck(ScriptedLake(
            "/Users/x/w/Cases/recheck_dec.lean:9:4: error: unknown constant\n",
            code=1), qualified=QUAL)
        check(not got.accepted, "a stored proof that now errors is refused")

        got = recheck(ScriptedLake(axioms_line(QUAL, *sorted(STANDARD_AXIOMS))),
                      qualified=QUAL)
        check(got.accepted and got.axioms == tuple(sorted(STANDARD_AXIOMS)),
              "the standard axioms are still standard on the recheck path")

        for label, exc in (
                ("a timeout", subprocess.TimeoutExpired("lake", 1)),
                ("lean not on PATH", OSError("No such file"))):
            got = recheck(ScriptedLake(raises=exc), qualified=QUAL)
            check(got.outcome == "not-run" and not got.ran,
                  f"{label} on the recheck path is not-run, not refuted")

        # The denylist reads the stored file too, and this is the path where
        # it matters most: `check` sees a file Attest generated, while this
        # one sees whatever came back out of the database.
        tampered = stored.replace(
            "theorem", "set_option debug.skipKernelTC true\ntheorem", 1)
        lake = ScriptedLake(axioms_line(QUAL))
        got = recheck(lake, source=tampered, qualified=QUAL)
        check(got.outcome == "refused" and not got.accepted,
              "a stored proof that switches the kernel off is refused")
        check(lake.lean_runs == 0, "...and never reaches Lean")

        # Exactly ONE `#print axioms` is exempt — the one every case file
        # carries. A second is a command the caller added.
        lake = ScriptedLake(axioms_line(QUAL))
        got = recheck(lake, source=stored + f"#print axioms {QUAL}\n",
                      qualified=QUAL)
        check(got.outcome == "refused",
              "a second #print in a stored file is not exempt")
        check(lake.lean_runs == 0, "...and it too never reaches Lean")

        # The file that was checked is the file that was stored, byte for
        # byte: the proof is evidence, so a path that rewrote it before
        # checking would be checking something else.
        lake = ScriptedLake(axioms_line(QUAL))
        got = recheck(lake, qualified=QUAL)
        check((tmp / "rc" / "Case_abc.lean").read_text() == stored,
              "the stored source is written through unchanged")
        check(got.source == stored, "the record carries the stored source")
        check(lake.builds == 0 and lake.lean_runs == 1,
              "the recheck path runs Lean once and builds nothing itself "
              "(materialize already built; runner.py sets _built_at)")

    if len(RAN) != EXPECTED:
        FAILURES.append(f"{len(RAN)} checks ran, not {EXPECTED}: a block "
                        f"stopped early, so later checks never ran")
    for f in FAILURES:
        print("  FAIL", f)
    print(f"{len(RAN) - len(FAILURES)}/{EXPECTED} kernel-decision checks "
          f"passed")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
