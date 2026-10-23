"""Golden outputs of the rule compiler, for every fixture rule.

    python3 tests/golden.py           # compare against tests/golden/compiler.json
    python3 tests/golden.py --write   # regenerate it (review the diff!)

What is pinned, per rule: the Lean module (held to the COMMITTED file in the
fixture's Lean package, `tests/fixtures/lean/`), the TypeQL
search, the shape and its hash, the double-negated collections, and — on
random snapshots that contain a witness — the proof term and the facts the
verdict relies on.

Why it matters: these outputs are stored. A changed TypeQL body for an
unchanged rule is permanent `Drift` on every existing database (`sync` only
deploys functions missing BY NAME); a changed shape hash orphans every stored
decision's `rule-shape`; a changed proof term means a stored case file no
longer regenerates byte for byte, so `recheck` fails. A refactor of
`rulec.py` has to leave all of them alone, and this is how that is checked.
"""

from __future__ import annotations

import json
import pathlib
import random
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))

from attest import rulec  # noqa: E402
from refeval import random_case  # noqa: E402
from schema_offline import model as offline_model  # noqa: E402

FIXTURES = HERE / "fixtures"
GOLDEN = HERE / "golden" / "compiler.json"

#: (domain, rule files, schema, Lean package, root namespace)
DOMAINS = [
    ("fixture", sorted((FIXTURES / "rules").glob("*.rule")),
     FIXTURES / "schema.tql", FIXTURES / "lean", "Fixture"),
]

#: random snapshots tried per rule, and witness-bearing ones kept
SEEDS, KEEP = 3000, 3


def rules():
    """(label, parsed rule, model, Lean package, root namespace)."""
    for _domain, paths, schema, lean, root in DOMAINS:
        model = offline_model(schema)
        for path in paths:
            yield (str(path.relative_to(ROOT)), rulec.load(path), model,
                   lean, root)


def outputs(rule, model, root) -> dict:
    out = {
        "lean": rulec.compile_lean(rule, model, f"{root}.Rules",
                                   f"{root}.Schema"),
        "typeql": rulec.compile_typeql(rule, model),
        "shape": rulec.shape(rule),
        "shape_sha": rulec.shape_sha(rule),
        "uses_as_of": rulec.uses_as_of(rule),
        "double_negated": rulec.double_negated_collections(rule),
        "fn_names": list(rulec.fn_names(rule)),
        "cases": [],
    }
    # small snapshots first; rules with several conditions rarely hold on
    # four rows per collection, so the search widens to eight
    tries = [(seed, 4) for seed in range(SEEDS)] + [
        (seed, 8) for seed in range(SEEDS, SEEDS + 8000)]
    for seed, size in tries:
        case = random_case(rule, model, random.Random(seed), size=size)
        found = case.witnesses()
        if not found:
            continue
        witness = list(found[0])
        # The SNAPSHOT is stored, not just the seed that produced it.
        # Storing `seed` alone coupled this file to the random generator:
        # any change to how `refeval.random_case` draws values changed the
        # snapshots, so the stored proof terms no longer matched and the
        # result read as "the compiler output differs from golden" — a
        # compiler regression that had not happened. `seed` and `size` are
        # kept for provenance only; `compare` reads `data`.
        out["cases"].append({
            "seed": seed, "size": size,
            "data": case.data, "scopes": case.scopes,
            "witness": witness,
            "proof": rulec.witness_proof(rule, model, case.data, witness),
            "relied": rulec.relied_facts(rule, model, case.data, witness,
                                         scopes=case.scopes),
        })
        if len(out["cases"]) == KEEP:
            break
    return out


def generate() -> dict:
    return {label: outputs(rule, model, root)
            for label, rule, model, _lean, root in rules()}


def compare() -> list[str]:
    """Every difference from the golden file and the committed Lean."""
    problems = []
    want = json.loads(GOLDEN.read_text())
    got = generate()
    for label, rule, model, lean, root in rules():
        committed = pathlib.Path(rulec.lean_path(
            rule, str(lean), f"{root}.Rules")).read_text()
        if got[label]["lean"] != committed:
            problems.append(f"{label}: Lean differs from the committed module")
        for key, value in got[label].items():
            if key in ("lean", "cases"):
                continue
            if want.get(label, {}).get(key) != value:
                problems.append(f"{label}: {key} differs from golden")
        # Cases are recomputed from the snapshot STORED in the golden file,
        # so what is compared is the compiler's output on fixed input. The
        # generator may change freely; only a real change in `witness_proof`
        # or `relied_facts` shows up here.
        for i, case in enumerate(want.get(label, {}).get("cases", [])):
            if "data" not in case:
                problems.append(f"{label}: case {i} has no stored snapshot; "
                                f"regenerate with --write")
                continue
            proof = rulec.witness_proof(rule, model, case["data"],
                                        case["witness"])
            relied = rulec.relied_facts(rule, model, case["data"],
                                        case["witness"],
                                        scopes=case["scopes"])
            if proof != case["proof"]:
                problems.append(f"{label}: case {i} proof term differs")
            if relied != case["relied"]:
                problems.append(f"{label}: case {i} relied facts differ")
    if set(want) != set(got):
        problems.append(f"rule set changed: {sorted(set(want) ^ set(got))}")
    return problems


def main(argv) -> int:
    if "--write" in argv:
        GOLDEN.parent.mkdir(exist_ok=True)
        data = generate()
        GOLDEN.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
        found = {k: len(v["cases"]) for k, v in data.items()}
        print(f"wrote {GOLDEN.relative_to(ROOT)}: witness cases per rule {found}")
        return 0
    problems = compare()
    for p in problems:
        print("  ", p)
    print("golden: OK" if not problems else f"golden: {len(problems)} differ")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
