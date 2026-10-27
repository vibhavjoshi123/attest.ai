"""Commit the counterexamples cx-0 finds, so the replay has something to read.

cx-0's done-when 1 asks that each historical defect be found, shrunk,
kernel-confirmed with standard axioms, **committed as a fixture, and replayed
in CI**. The first three held; the fixtures did not exist, and
`test_counterexamples.py`'s replay reads

    files = sorted(FIXTURES.rglob("*.json"))
    if not files:
        return

so on an empty directory it passed without checking anything. An unrun check
reads as coverage, which is worse than no check — the same reason e2e stage 12
was rewritten. This writes the fixtures that make it real.

Writing one needs Lean: a fixture is only committed once the kernel has agreed
about every verdict the violation rests on. That confirmation cannot happen
against a domain package, where the `Iff.rfl` binding correctly refutes a
mutant's verdict, so it goes through a `ScratchPackage` in which the mutant is
the rule (see `attest/search/lean.py`).

    python3 tests/make_counterexamples.py --write   # search, confirm, write
    python3 tests/make_counterexamples.py           # re-find each committed one

The default mode needs no Lean. It re-runs the search and checks that every
committed signature is still produced, which is what catches a search that
has stopped finding a defect it used to find.
"""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tests"),
                str(ROOT / "tests" / "fixtures")]

from attest import rulec                                          # noqa: E402
from attest.kernel import STANDARD_AXIOMS                         # noqa: E402
from attest.props import parse_family, validate                   # noqa: E402
from attest.search.cx import search as cx                         # noqa: E402

import schema_offline                                             # noqa: E402

HERE = pathlib.Path(__file__).resolve().parent
FIXTURES = HERE / "counterexamples"
RULES = ROOT / "tests" / "fixtures" / "rules"
MUTANTS = HERE / "mutants" / "fixture"
BAND = ("latest-high", "latest-low")

HISTORICAL = str(MUTANTS / "historical-{}.rule")
DEFECT2 = str(MUTANTS / "defect2-{}.rule")

#: One entry per historical defect, with the search budget that finds it.
#: `status` is read by the replay: `historical` means the rules that produced
#: it are mutants kept as evidence, so the fixture records a defect that was
#: fixed rather than one that is open.
CASES = (
    {"defect": 1, "property": "fixture.alpha-band.exclusive",
     "rules_pattern": HISTORICAL, "status": "historical",
     "kw": {"max_rows": 2, "limit": 4000, "stop_after": 3},
     "says": "two readings on the same day fire both branches at once"},
    {"defect": 2, "property": "fixture.reingestion.stable-add",
     "rules_pattern": DEFECT2, "status": "historical",
     "kw": {"max_rows": 1, "limit": 3000, "stop_after": 3},
     "says": "an exact duplicate on re-ingestion silences a branch"},
    {"defect": 3, "property": "fixture.alpha-band.stable-add",
     "rules_pattern": HISTORICAL, "status": "historical",
     "kw": {"max_rows": 1, "limit": 2000, "stop_after": 3},
     "says": "a reading dated after the decision changes a settled verdict"},
)


def model():
    return schema_offline.model(ROOT / "tests" / "fixtures" / "schema.tql")


def declaration(prop_id: str):
    decls = [d for f in RULES.glob("*.family")
             for d in parse_family(f.read_text())]
    validate(decls, {p.stem for p in RULES.glob("*.rule")})
    found = [d for d in decls if d.id == prop_id]
    if not found:
        raise SystemExit(f"no declaration {prop_id}")
    return found[0]


def rules(pattern: str):
    return {n: rulec.load(pattern.format(n)) for n in BAND}


def find(case) -> list:
    return cx.search(declaration(case["property"]),
                     rules(case["rules_pattern"]), model(), **case["kw"])


def fixture_lean():
    from attest.domain import LeanPackage
    return LeanPackage(directory=ROOT / "tests" / "fixtures" / "lean",
                       root_module="Fixture",
                       schema_namespace="Fixture.Schema",
                       rules_namespace="Fixture.Rules",
                       theorem_modules=("Fixture.Properties",))


def confirm(violation, case, workdir: pathlib.Path) -> dict:
    """Kernel-confirm one violation in a package where the mutant is the rule."""
    from attest.search.lean import Acceptor, ScratchPackage

    lean = fixture_lean()
    rs = rules(case["rules_pattern"])
    extra = {rulec.module(r, lean.rules_namespace):
             rulec.compile_lean(r, model(), lean.rules_namespace,
                                lean.schema_namespace)
             for r in rs.values()}
    pkg = ScratchPackage.build(lean, extra, workdir / "pkgs",
                               drop=lean.theorem_modules)
    acceptor = Acceptor(workdir / "cases")
    return cx.confirm(violation, rs, model(), pkg.lean, acceptor.bind(pkg))


def path_for(case, violation) -> pathlib.Path:
    return (FIXTURES / "fixture" / case["property"]
            / f"{violation.signature[:12]}.json")


def write() -> int:
    """Search, confirm with the kernel, and write one fixture per defect."""
    written, failures = [], []
    with tempfile.TemporaryDirectory(prefix="attest-cx-fixtures-") as tmp:
        tmp = pathlib.Path(tmp)
        for case in CASES:
            found = find(case)
            if not found:
                failures.append(f"defect {case['defect']}: not found")
                continue
            violation = found[0]
            report = confirm(violation, case, tmp)
            verdicts = {k: v for k, v in report.items()
                        if not k.startswith("_")}
            if not report.get("_confirmed"):
                failures.append(
                    f"defect {case['defect']}: not kernel-confirmed: "
                    + repr({k: (v["outcome"], v["reason"])
                            for k, v in verdicts.items()})
                    + " unchecked: " + repr(report.get("_unchecked")))
                continue
            axioms = sorted({a for v in verdicts.values()
                             for a in v["axioms"]})
            if not set(axioms) <= set(STANDARD_AXIOMS):
                failures.append(f"defect {case['defect']}: axioms {axioms}")
                continue
            # The kernel report is kept for the record, but not the proof
            # terms or the case sources: a fixture is a world, not a proof.
            record = violation.as_dict()
            record.pop("kernel", None)
            record.update(
                defect=case["defect"], says=case["says"],
                rules_pattern=_portable(case["rules_pattern"]),
                status=case["status"],
                kernel={"confirmed": True, "axioms": axioms,
                        "rules": sorted(verdicts)})
            out = path_for(case, violation)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
            written.append(out)
            print(f"  defect {case['defect']}: {out.relative_to(HERE)} "
                  f"(axioms {axioms})")
    for f in failures:
        print("  FAIL", f)
    print(f"{len(written)} fixture(s) written, {len(failures)} failed")
    return 1 if failures else 0


def _portable(pattern: str) -> str:
    """Store the rule pattern relative to the repository, not to this machine."""
    return str(pathlib.Path(pattern).relative_to(ROOT))


def check() -> int:
    """Every committed fixture is still found by the search that produced it."""
    files = sorted(FIXTURES.rglob("*.json"))
    if not files:
        print("no fixtures committed: run with --write")
        return 1
    failures = []
    by_property: dict[str, set[str]] = {}
    for path in files:
        data = json.loads(path.read_text())
        by_property.setdefault(data["property"], set()).add(data["signature"])
    for case in CASES:
        want = by_property.get(case["property"], set())
        if not want:
            failures.append(f"defect {case['defect']}: no fixture committed")
            continue
        got = {v.signature for v in find(case)}
        missing = want - got
        if missing:
            failures.append(
                f"defect {case['defect']} ({case['property']}): the search no "
                f"longer finds {sorted(missing)}; it found {sorted(got)}")
    for f in failures:
        print("  FAIL", f)
    print(f"{len(files) - len(failures)}/{len(files)} committed "
          f"counterexamples re-found")
    return 1 if failures else 0


def main(argv) -> int:
    if argv and argv[0] == "--write":
        return write()
    return check()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
