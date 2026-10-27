"""Does the suite have teeth? Break the system on purpose and find out.

Every other test in this tree asks whether Attest is right. This one asks
whether the tests would notice if it stopped being right — which is a
different question, and the only one that measures the suite rather than the
system. Five tests in this repository have passed while testing nothing: a
replay over an empty fixture directory, seven example runners that asserted
nothing, five suites no pipeline ran, a hardcoded assertion total that read
"26/26" while 24 checks ran, and artifact pins that would have passed on
four stale artifacts. None of them failed. They were all green.

So: one deliberate defect at a time, each a real weakening of a capability
the system claims, each named with the suite that must notice it. Apply the
defect to a throwaway copy of the tree, run that suite, and require it to
fail. A mutant that SURVIVES is a capability nothing checks — the suite
reports green on a system that no longer works, which is worse than having
no test at all, because people believe it.

Three disciplines make this honest rather than decorative:

  1. **The named suite must be the one that kills it.** Not "something
     somewhere went red". A mutant killed only by a suite that happens to
     import the module tells you nothing about where the coverage is.
  2. **A patch that no longer applies is a failure.** The classic silent
     death of a mutation harness is a refactor that makes every patch a
     no-op: nothing applies, nothing survives, and it prints all-killed for
     ever. Each `old` must occur exactly once in the file.
  3. **Every suite is run clean first.** A suite that was already failing
     would "kill" every mutant assigned to it without reading any of them.

Mutants are tiered by what they need. `offline` runs here in seconds;
`lean` needs a Lean toolchain; `live` needs a TypeDB server. The summary
says exactly how many of each were judged, because a tier that silently
did not run is the same lie in a smaller font.

    python3 tests/test_mutation.py              # the offline tier
    python3 tests/test_mutation.py --all        # everything available
    python3 tests/test_mutation.py --list
    python3 tests/test_mutation.py --only k.    # one capability
    python3 tests/test_mutation.py --keep       # leave the trees to inspect
"""

from __future__ import annotations

import concurrent.futures
import dataclasses
import os
import pathlib
import queue
import shutil
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
#: where the throwaway trees go. Never inside the repository: a copy of the
#: tree under the tree is a copy of the copy.
SCRATCH = pathlib.Path(os.environ.get(
    "ATTEST_MUTATION_TREES",
    os.environ.get("TMPDIR", "/tmp"))) / "attest-mutation"


@dataclasses.dataclass(frozen=True)
class Mutant:
    #: short id; the prefix groups it by capability
    id: str
    #: what this defect lets through, in one line — the capability at stake
    capability: str
    path: str
    old: str
    new: str
    #: the suite that must notice. Not "a suite": this one.
    suite: str
    needs: str = "offline"


KERNEL = "tests/test_kernel_decision.py"
CORE = "tests/test_core.py"
PROPS = "tests/test_search_props.py"
PIPELINE = "tests/test_search_pipeline.py"
GENERATORS = "tests/test_search_generators.py"
COUNTEREXAMPLES = "tests/test_counterexamples.py"
GOLDEN = "tests/golden.py"
BRIDGE = "tests/test_bridge.py"

MUTANTS: list[Mutant] = [

    # ── the kernel's verdict ──────────────────────────────────────────
    # Everything downstream is this function's answer carried forward. A
    # defect here is a decision the system says Lean approved when it did
    # not, and no later stage can detect it.
    Mutant(
        id="k.masked",
        capability="a masked or missing axioms report is read as clean",
        path="attest/kernel.py", suite=KERNEL,
        old="        masked = len(reports) != 1 or len(own) != 1",
        new="        masked = False",
    ),
    Mutant(
        id="k.subset",
        capability="an axiom outside the allowed set is accepted",
        path="attest/kernel.py", suite=KERNEL,
        old="                    and used <= self.allowed_axioms)",
        new="                    and True)",
    ),
    Mutant(
        id="k.sorry",
        capability="a proof that uses `sorry` is accepted",
        path="attest/kernel.py", suite=KERNEL,
        old='        has_sorry = ("declaration uses \'sorry\'" in log '
            'or "sorryAx" in log)',
        new="        has_sorry = False",
    ),
    Mutant(
        id="k.error-word",
        capability="the error scan matches the path, not the diagnostic",
        path="attest/kernel.py", suite=KERNEL,
        old='                      if re.search(r":\\s*error:", line)), None)',
        new='                      if "error" in line), None)',
    ),
    Mutant(
        id="k.timeout",
        capability="a check that never finished is reported as a rejection",
        path="attest/kernel.py", suite=KERNEL,
        old='                file=self._shown(path), source=source, '
            'outcome="not-run")',
        new='                file=self._shown(path), source=source, '
            'outcome="refuted")',
    ),
    Mutant(
        id="k.build-closed",
        capability="proofs are checked against a package that did not build",
        path="attest/kernel.py", suite=KERNEL,
        old="        if completed.returncode != 0:\n"
            "            raise BuildFailed(\n"
            '                "the Lean package does not build',
        new="        if False:\n"
            "            raise BuildFailed(\n"
            '                "the Lean package does not build',
    ),
    Mutant(
        id="k.denylist-check",
        capability="a generated case file reaches Lean without the denylist "
                   "reading it",
        path="attest/kernel.py", suite=KERNEL,
        old="        bad = forbidden(probe)\n"
            "        if bad is not None:\n"
            "            result = Check(",
        new="        bad = None\n"
            "        if bad is not None:\n"
            "            result = Check(",
    ),
    Mutant(
        id="k.denylist-recheck",
        capability="a proof read back out of the store reaches Lean "
                   "unexamined — the path whose input Attest did not write",
        path="attest/kernel.py", suite=KERNEL,
        old="        bad = forbidden(probe)\n"
            "        if bad is not None:\n"
            '            return Check(theorem=theorem, name=theorem, '
            'statement="",',
        new="        bad = None\n"
            "        if bad is not None:\n"
            '            return Check(theorem=theorem, name=theorem, '
            'statement="",',
    ),

    # ── the verdict again, on the re-verification path ────────────────
    # `check_source` is a SECOND implementation of the acceptance
    # arithmetic, for files read back out of the store. Two copies of one
    # predicate drift, and this one drifted once already: it accepted a
    # clean report that belonged to another theorem.
    Mutant(
        id="cs.named",
        capability="a stored proof is accepted on another theorem's clean "
                   "axioms report",
        path="attest/kernel.py", suite=KERNEL,
        old="        named = bool(lines) and (",
        new="        named = True or (",
    ),
    Mutant(
        id="cs.one-report",
        capability="a stored proof with no report, or several, is accepted",
        path="attest/kernel.py", suite=KERNEL,
        old="              and len(lines) == 1 and named",
        new="              and named",
    ),
    Mutant(
        id="cs.subset",
        capability="a stored proof may lean on any axiom it likes",
        path="attest/kernel.py", suite=KERNEL,
        # anchored on the line above as well: the same text, differently
        # indented, is also the tail of `check`'s own acceptance test, and
        # a substring that matches twice is a patch this harness refuses
        old="              and len(lines) == 1 and named\n"
            "              and used <= self.allowed_axioms)",
        new="              and len(lines) == 1 and named\n"
            "              and True)",
    ),
    Mutant(
        id="cs.sorry",
        capability="a stored proof that now uses `sorry` still re-verifies",
        path="attest/kernel.py", suite=KERNEL,
        old='        sorry = "declaration uses \'sorry\'" in log '
            'or "sorryAx" in log',
        new="        sorry = False",
    ),
    Mutant(
        id="k.report-spelling",
        capability="an axiom-free proof is read as having no report at all",
        path="attest/kernel.py", suite=KERNEL,
        old=r"""    r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",""",
        new=r"""    r"'([\w.]+)' (?:depends on axioms: \[(.*?)\])",""",
    ),

    # ── what may appear in a Lean file at all ─────────────────────────
    # The denylist is the only thing between a stored snapshot and a
    # `set_option debug.skipKernelTC true` that turns the kernel off.
    Mutant(
        id="k.char-literal",
        capability="a Lean character literal hides a kernel-skipping option",
        path="attest/kernel.py", suite=CORE,
        old=r"""    code = re.sub(r"'(?:\\.|[^'\\])'", "'x'", source)""",
        new="    code = source",
    ),
    Mutant(
        id="k.native-decide",
        capability="`native_decide` compiles the proof away from the kernel",
        path="attest/kernel.py", suite=CORE,
        old=r"""    r"@\[extern|\bnative_decide\b|\bunsafe\b|\bpartial\b|\baxiom\b|""",
        new=r"""    r"@\[extern|\bnot_a_real_token\b|\bunsafe\b|\bpartial\b|\baxiom\b|""",
    ),
    Mutant(
        id="k.set-option",
        capability="`set_option` reaches Lean, including the one that skips "
                   "the kernel",
        path="attest/kernel.py", suite=CORE,
        old=r"""    r"\bset_option\b|skipKernelTC|#eval|#print\b|\brun_cmd\b|\brun_tac\b|""",
        new=r"""    r"skipKernelTC|#eval|#print\b|\brun_cmd\b|\brun_tac\b|""",
    ),

    # ── the compiler: what a .rule file is allowed to compile to ──────
    # `rulec` is the authority on what a rule MEANS, and the per-case
    # differential cannot see a mistake both compiled forms share. These
    # are the guards that stop a rule compiling to something vacuous or
    # to something that is not a rule at all.
    Mutant(
        id="rc.empty-body",
        capability="an empty rule body compiles to `Prop := True`, so an "
                   "Eligible-style conclusion approves everyone with a real "
                   "kernel proof",
        path="attest/rulec.py", suite=CORE,
        old='    if not any(s["kind"] == "some" for s in r["steps"]):',
        new="    if False:",
    ),
    Mutant(
        id="rc.says-comment",
        capability="a `says` sentence closes the Lean comment it is written "
                   "into and the rest of the line becomes code",
        path="attest/rulec.py", suite=CORE,
        old='    if "-/" in text or "/-" in text:',
        new="    if False:",
    ),
    Mutant(
        id="rc.conclusion-ident",
        capability="a conclusion that is not an identifier is interpolated "
                   "into the theorem statement anyway",
        path="attest/rulec.py", suite=CORE,
        old='    if not _IDENT_RE.match(r["conclusion"]):',
        new="    if False:",
    ),
    Mutant(
        id="rc.all-steps",
        capability="every check that walks a rule stops at the top level, "
                   "exempting whatever is written inside a `none of` — which "
                   "is where a rule hides its hardest conditions",
        path="attest/rulec.py", suite=CORE,
        old='        if s["kind"] == "none":\n'
            "            yield from all_steps(s[\"steps\"])",
        new="        if False:\n"
            "            yield from all_steps(s[\"steps\"])",
    ),

    # ── the type bridge: what a snapshot may say to Lean ──────────────
    # The two soundness holes the attack tests found. Both let a false
    # statement be PROVED: Lean's kernel was never wrong, it was asked the
    # wrong question.
    Mutant(
        id="b.surrogate",
        capability="a non-BMP string is split into surrogate halves, which "
                   "Lean reads as U+0000 — so two different strings prove equal",
        path="attest/typebridge.py", suite=BRIDGE,
        old="        elif 0xD800 <= cp <= 0xDFFF:",
        new="        elif False:",
    ),
    Mutant(
        id="b.forged-schema",
        capability="a Schema.lean edited to change how a numeral reads passes "
                   "as the rendering of the live schema, keeping its hash line",
        path="attest/typebridge.py", suite=BRIDGE,
        old="    if on_disk != expected:",
        new="    if False:",
    ),

    # ── the trust boundary ────────────────────────────────────────────
    # The core must not import the search: the search is untrusted, and a
    # core that can reach it can be steered by it.
    Mutant(
        id="t.core-imports-search",
        capability="the trusted core imports the untrusted search",
        path="attest/runner.py", suite=CORE,
        old="from . import rulec, typebridge",
        new="from . import rulec, typebridge\nfrom attest.search import cx",
    ),

    # ── the pipeline itself ───────────────────────────────────────────
    # The failure that happened five times: a suite that nothing runs. The
    # line in the coverage report still says it is covered, which is why
    # this is worse than having no test.
    Mutant(
        id="e.suite-dropped",
        capability="a suite is quietly dropped from the pipeline and still "
                   "reads as coverage",
        path="scripts/check.sh", suite=CORE,
        old='  "$PY" tests/test_search_pipeline.py || return 1',
        new="  true || return 1",
    ),

    # ── property declarations ─────────────────────────────────────────
    Mutant(
        id="p.unknown-rule",
        capability="a family may name a rule that does not exist",
        path="attest/props.py", suite=PROPS,
        old="        unknown = [r for r in decl.rules if r not in known]",
        new="        unknown = []",
    ),
    Mutant(
        id="p.gate",
        capability="a gate may name something that is not a rule",
        path="attest/props.py", suite=PROPS,
        old="        if decl.gate is not None and decl.gate not in known:",
        new="        if False:",
    ),

    # ── the search: which worlds count as a counterexample ────────────
    # These decide what the search reports. Too loose and every correct
    # rule is reported broken; too tight and real defects are never found.
    # Both failures look like a working search from the outside.
    Mutant(
        id="s.needs-change",
        capability="`stable-retract` is screened as if it were not a change",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old='    return decl.kind in ("stable-add", "stable-retract")',
        new='    return decl.kind in ("stable-add",)',
    ),
    Mutant(
        id="s.screen-no-before",
        capability="a change candidate with no before-world is screened "
                   "as violating",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old="        if cand.before is None:\n            return False, {}, None",
        new="        if cand.before is None:\n            return True, {}, None",
    ),
    Mutant(
        id="s.scope-no-before",
        capability="a candidate that changed nothing is in scope anyway",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old="    if cand.before is None:\n        return False\n    for coll in",
        new="    if cand.before is None:\n        return True\n    for coll in",
    ),
    Mutant(
        id="s.retract-branch",
        capability="a retraction is never recognised as the change in question",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old='        if decl.kind == "stable-retract":',
        new="        if False:",
    ),
    Mutant(
        id="s.retract-when",
        capability="the `when` filter is ignored on the retraction branch, "
                   "so every correct rule is reported broken",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old='                if row.get("retracted-at") and matches_when(\n'
            "                        row, decl.when, cand.ws.as_of_day):",
        new='                if row.get("retracted-at") and True:',
    ),
    Mutant(
        id="s.when-added",
        capability="the `when` filter is ignored on added rows",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old="            if matches_when(row, decl.when, cand.ws.as_of_day):\n"
            "                return True",
        new="            if True:\n                return True",
    ),
    Mutant(
        id="s.duplicate",
        capability="a duplicate-row declaration never matches a duplicate",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old='            if (decl.when or "").strip() == DUPLICATE:',
        new="            if False:",
    ),
    Mutant(
        id="s.signature-factid",
        capability="the fact-id leaks into the signature, so one defect is "
                   "reported once per id",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old="        shape.append((coll, tuple(sorted(set(atoms))),",
        new='        shape.append((coll, row.get("fact-id"), '
            "tuple(sorted(set(atoms))),",
    ),
    Mutant(
        id="s.readings-mispair",
        capability="the world after a change is paired with the verdicts "
                   "before it, so the kernel is asked about a claim nobody made",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old='            ("@after", violation.world, violation.verdicts_after)]',
        new='            ("@after", violation.world, violation.verdicts)]',
    ),
    Mutant(
        id="s.confirm-vacuous",
        capability="a violation the kernel was never asked about is confirmed",
        path="attest/search/cx/search.py", suite=PIPELINE,
        old='    out["_confirmed"] = (bool(checks) and not unchecked',
        new='    out["_confirmed"] = (not unchecked',
    ),
    Mutant(
        id="s.unchecked-guard",
        capability="a rule read on one side of a change only is confirmed",
        path="attest/search/cx/search.py", suite=COUNTEREXAMPLES,
        old='        return {"_unchecked": unchecked, "_confirmed": False}',
        new='        unchecked = []',
    ),

    # ── the generators: the guards that keep the search bounded ───────
    # A guard that stops guarding fails nothing. The search gets slower,
    # or noisier, or unbounded, and the counterexamples still look fine.
    Mutant(
        id="g.retract-guard",
        capability="a row is retracted twice, a world the store refuses",
        path="attest/search/cx/generators.py", suite=GENERATORS,
        old='    if row.get("retracted-at"):\n        return None',
        new="    if False:\n        return None",
    ),
    Mutant(
        id="g.foreign-guard",
        capability="a collection with nothing to scope is 'made foreign' "
                   "and screened unchanged",
        path="attest/search/cx/generators.py", suite=GENERATORS,
        old="    if not via or row.get(via) is None:\n        return None",
        new="    if False:\n        return None",
    ),
    Mutant(
        id="g.limit",
        capability="small-scope enumeration is unbounded",
        path="attest/search/cx/generators.py", suite=GENERATORS,
        old="                if made > limit:\n                    return",
        new="                if False:\n                    return",
    ),
    Mutant(
        id="g.future-empty",
        capability="a generator raises on an empty collection and ends the "
                   "whole search",
        path="attest/search/cx/generators.py", suite=GENERATORS,
        old="        if coll not in ws.data or not ws.data[coll]:\n"
            "            continue",
        new="        if False:\n            continue",
    ),
    Mutant(
        id="g.day-attribute",
        capability="a future-dated row is dated in one domain's attribute "
                   "name, so in every other domain it is the old row again",
        path="attest/search/cx/generators.py", suite=GENERATORS,
        old="                        found.add(attr)",
        new='                        found.add("effective-day")',
    ),
    Mutant(
        id="g.scope-fields",
        capability="generated rows are not the subject's, so a rule that "
                   "ignores whose record it is looks correct",
        path="attest/search/cx/generators.py", suite=GENERATORS,
        old='        if c["name"] == coll_name and c.get("via"):\n'
            '            return {c["via"]: "s1"}',
        new="        if False:\n"
            '            return {c["via"]: "s1"}',
    ),

    # ── the shipped rules, and the artifacts that quote them ──────────
    # A changed rule is a changed claim. The goldens are what turn that
    # into a reviewable diff rather than a silent change of meaning.
    Mutant(
        id="r.fixture-threshold",
        capability="a shipped rule's threshold changes with nothing to show it",
        path="tests/fixtures/rules/latest-high.rule", suite=GOLDEN,
        old="  require r.amount >= 70",
        new="  require r.amount >= 60",
    ),
]

def available(needs: str) -> bool:
    if needs == "offline":
        return True
    if needs == "lean":
        return shutil.which("lake") is not None
    return bool(os.environ.get("TYPEDB_ADDRESS"))


def build_tree(dest: pathlib.Path) -> pathlib.Path:
    """A throwaway copy of the tree. The working tree is never touched.

    `.git` is copied so a suite that reads the history can; the Lake
    build directories are not, because nothing offline reads them and they
    are most of the bytes.
    """
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        shutil.rmtree(dest)
    skip = (".lake", "__pycache__")
    if shutil.which("rsync"):
        excludes = [arg for name in (*skip, "*.pyc")
                    for arg in ("--exclude", name)]
        done = subprocess.run(
            ["rsync", "-a", *excludes, f"{ROOT}/", f"{dest}/"],
            capture_output=True, text=True)
        if done.returncode != 0:
            raise RuntimeError(f"could not copy the tree: {done.stderr[:300]}")
        return dest
    # No rsync (some CI images), so do it in Python. Slower, same result.
    shutil.copytree(ROOT, dest, symlinks=True,
                    ignore=shutil.ignore_patterns(*skip, "*.pyc"))
    return dest


def run_suite(tree: pathlib.Path, suite: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, suite], cwd=tree,
                          capture_output=True, text=True, timeout=900)


def judged(out: str) -> bool:
    """Did the suite run to completion, or crash on the way in?

    A mutant that stops a module importing is killed by every suite that
    imports it, which says nothing about coverage. Distinguishing the two
    keeps the report honest: a crash is a kill, but a weak one.

    Read off the traceback, not off the shape of the summary line: the
    first version looked for `n/m`, which `tests/golden.py` does not print,
    so a suite that reported the defect perfectly well was filed as having
    crashed.
    """
    return "Traceback (most recent call last)" not in out


def apply_to(tree: pathlib.Path, m: Mutant) -> str:
    """Patch one file, returning the original text. Raises if the patch
    does not apply exactly once."""
    path = tree / m.path
    text = path.read_text()
    found = text.count(m.old)
    if found != 1:
        raise AssertionError(
            f"the mutation no longer applies: {found} occurrences of its "
            f"anchor in {m.path} (expected exactly 1). The code moved; the "
            f"mutant must move with it, or this harness is measuring nothing")
    path.write_text(text.replace(m.old, m.new, 1))
    return text


def self_check() -> list[str]:
    """The harness's own failure modes, checked on every run.

    Both of these have already bitten. A patch whose anchor matches twice
    is refused rather than applied to the wrong line — and when that
    happened it was reported in the same breath as a surviving mutant,
    which sent me looking for a missing test that was already there. And
    `judged` first looked for an `n/m` summary line, which `tests/golden.py`
    does not print, so a suite that reported the defect perfectly well was
    filed as having crashed.
    """
    import tempfile
    out = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        (tmp / "f.py").parent.mkdir(parents=True, exist_ok=True)
        (tmp / "f.py").write_text("x = 1\nx = 1\n")
        twice = Mutant(id="t", capability="", path="f.py", old="x = 1",
                       new="x = 2", suite="s")
        try:
            apply_to(tmp, twice)
        except AssertionError:
            pass
        else:
            out.append("a patch matching twice was applied anyway")
        if (tmp / "f.py").read_text() != "x = 1\nx = 1\n":
            out.append("a refused patch still changed the file")
        missing = Mutant(id="t", capability="", path="f.py",
                         old="not in the file", new="y", suite="s")
        try:
            apply_to(tmp, missing)
        except AssertionError:
            pass
        else:
            out.append("a patch matching nothing was applied anyway")
    if judged("Traceback (most recent call last):\n  File ..."):
        out.append("a traceback was read as a suite that ran")
    if not judged("golden: 1 differ"):
        out.append("a suite that reported a difference was read as a crash")
    if not judged("  FAIL something\n\n3/4 passed"):
        out.append("a suite that failed a check was read as a crash")
    for suite in sorted({m.suite for m in MUTANTS}):
        if not (ROOT / suite).exists():
            out.append(f"no such suite: {suite}")
    ids = [m.id for m in MUTANTS]
    if len(set(ids)) != len(ids):
        out.append("duplicate mutant ids")
    return out


def main(argv: list[str]) -> int:
    only = None
    for n, arg in enumerate(argv):
        if arg.startswith("--only="):
            only = arg.split("=", 1)[1]
        elif arg == "--only":
            only = argv[n + 1] if n + 1 < len(argv) else None
    tiers = ("offline", "lean", "live") if "--all" in argv else ("offline",)
    chosen = [m for m in MUTANTS
              if m.needs in tiers and (not only or m.id.startswith(only))]

    if "--list" in argv:
        for m in MUTANTS:
            print(f"  {m.id:24} {m.needs:8} {m.suite.split('/')[-1]:30} "
                  f"{m.capability}")
        print(f"\n{len(MUTANTS)} mutants")
        return 0

    skipped = [m for m in MUTANTS if m.needs in tiers and not available(m.needs)]
    chosen = [m for m in chosen if available(m.needs)]
    if not chosen:
        print("no mutants selected")
        return 2

    broken = self_check()
    for problem in broken:
        print(f"  FAIL the harness itself: {problem}")
    if broken:
        return 2

    workers = int(os.environ.get("ATTEST_MUTATION_WORKERS", "4"))
    workers = max(1, min(workers, len(chosen)))
    print(f"{len(chosen)} mutants, {workers} tree(s)")

    trees: queue.Queue[pathlib.Path] = queue.Queue()
    started = time.time()
    for n in range(workers):
        trees.put(build_tree(SCRATCH / f"tree{n}"))
    print(f"  copied {workers} tree(s) in {time.time() - started:.1f}s")

    # Every suite, clean, before anything is broken. A suite that was
    # already red would "kill" every mutant assigned to it without reading
    # a single one.
    control: dict[str, int] = {}
    base = trees.get()
    try:
        for suite in sorted({m.suite for m in chosen}):
            done = run_suite(base, suite)
            control[suite] = done.returncode
            if done.returncode == 3:
                # The repository's own code for "the infrastructure failed,
                # not the system" — a suite returns it when it cannot judge,
                # e.g. a missing tool. Its mutants cannot be judged here, and
                # saying so beats both failing and quietly passing.
                print(f"  {suite} cannot judge anything in this checkout "
                      f"(exit 3); its mutants are not judged")
            elif done.returncode != 0:
                print(f"  FAIL control: {suite} exits {done.returncode} on "
                      f"an unmutated tree, so it cannot judge anything\n"
                      f"{done.stdout[-600:]}")
    finally:
        trees.put(base)
    if any(code not in (0, 3) for code in control.values()):
        return 1
    blind = {s for s, code in control.items() if code == 3}
    skipped += [m for m in chosen if m.suite in blind]
    chosen = [m for m in chosen if m.suite not in blind]
    if not chosen:
        print("no suite here can judge any mutant")
        return 3
    print(f"  {len(control) - len(blind)} suite(s) green on the unmutated "
          f"tree ({time.time() - started:.1f}s)")

    results: dict[str, tuple[str, str]] = {}

    def one(m: Mutant) -> None:
        tree = trees.get()
        try:
            original = apply_to(tree, m)
            try:
                done = run_suite(tree, m.suite)
            finally:
                (tree / m.path).write_text(original)
            out = done.stdout + done.stderr
            if done.returncode == 0:
                results[m.id] = ("SURVIVED", "the suite passed anyway")
            elif judged(out):
                first = next((ln.strip() for ln in out.splitlines()
                              if "FAIL" in ln or "dead" in ln), "")
                results[m.id] = ("killed", first[:96])
            else:
                results[m.id] = ("killed (crash)",
                                 "the suite did not run to completion")
        except AssertionError as exc:
            results[m.id] = ("NOT APPLIED", str(exc)[:120])
        except Exception as exc:                                # noqa: BLE001
            results[m.id] = ("ERROR", f"{type(exc).__name__}: {exc}"[:120])
        finally:
            trees.put(tree)

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        list(pool.map(one, chosen))

    bad = []
    for m in chosen:
        verdict, detail = results[m.id]
        flag = " " if verdict.startswith("killed") else "!"
        print(f"{flag} {verdict:14} {m.id:24} {m.suite.split('/')[-1]:30} "
              f"{m.capability}")
        if verdict != "killed":
            print(f"      {detail}")
        if not verdict.startswith("killed"):
            bad.append(m)

    for m in skipped:
        why = ("its suite cannot judge anything here" if m.suite in blind
               else f"needs {m.needs}")
        print(f"  not judged    {m.id:24} {why}")

    if "--keep" not in argv:
        # ~95MB per tree, and four of them by default. Left behind in TMPDIR
        # they are invisible until a disk fills up.
        shutil.rmtree(SCRATCH, ignore_errors=True)

    killed = len(chosen) - len(bad)
    print(f"\n{killed}/{len(chosen)} mutants killed by the suite named for "
          f"them, in {time.time() - started:.0f}s")
    survived = [m for m in bad if results[m.id][0] == "SURVIVED"]
    stale = [m for m in bad if results[m.id][0] != "SURVIVED"]
    if survived:
        print("a surviving mutant is a capability nothing checks:")
        for m in survived:
            print(f"  {m.id}: {m.capability}")
    if stale:
        # Not the same failure at all, and reporting them together sent me
        # looking for a missing test when the anchor had simply moved.
        print("these mutants never ran, so they measured nothing:")
        for m in stale:
            print(f"  {m.id}: {results[m.id][0]} — {results[m.id][1]}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
