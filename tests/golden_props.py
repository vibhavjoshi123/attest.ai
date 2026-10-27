"""Pin every declaration the repository ships.

`attest/props.py` is trusted for the soundness of a *claim*: what a
property says is whatever generates it. Review 2 finding 15 asks for four
things, and this file is the fourth — the output pinned for every shipped
declaration, so a change to the parser shows up as a diff on a reviewed
file rather than as a quietly different claim.

The other three hold already: `predicate` lives in
`attest/search/cx/props_eval.py` and not here (finding 4c), `props.py` is
well inside its ~600-line budget, and `parse_family` has its own must-fail
corpus in `tests/must_fail/family/`.

What is NOT pinned here yet is the Lean statement each declaration
generates, because `family_module` does not exist until the property
prover. When it does, its output belongs in this file too, and the
kernel/predicate cross-check of Review 2 finding 4a becomes possible —
that cross-check is the thing that makes keeping the two readings apart
worth anything.

    python3 tests/golden_props.py            # compare
    python3 tests/golden_props.py --write    # re-pin
"""

from __future__ import annotations

import dataclasses
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from attest.props import parse_family, validate                   # noqa: E402

GOLDEN = pathlib.Path(__file__).resolve().parent / "golden" / "props.json"


def families() -> list[pathlib.Path]:
    return sorted((ROOT / "tests" / "fixtures" / "rules").rglob("*.family"))


def generate() -> dict:
    out: dict[str, dict] = {}
    for path in families():
        rel = str(path.relative_to(ROOT))
        decls = parse_family(path.read_text())
        rules = {p.stem for p in path.parent.glob("*.rule")}
        validate(decls, rules)
        out[rel] = {
            "rules_available": sorted(rules),
            "declarations": [dataclasses.asdict(d) for d in decls],
        }
    return out


def compare() -> list[str]:
    problems: list[str] = []
    if not GOLDEN.exists():
        return [f"{GOLDEN.relative_to(ROOT)} is missing; run --write"]
    # Both sides through JSON. A `PropertyDecl` holds tuples, JSON writes
    # them as arrays and reads them back as lists, so comparing the pinned
    # file against a fresh `generate()` reported every tuple field as
    # changed. This is the second pin in this repository to trip on it —
    # `tests/test_search_world.py` was the first — which is why the
    # normalisation is a named step and not an inline `json.loads`.
    want = json.loads(GOLDEN.read_text())
    got = json.loads(json.dumps(generate()))
    for rel in sorted(set(want) | set(got)):
        if rel not in want:
            problems.append(f"{rel}: new, not pinned")
        elif rel not in got:
            problems.append(f"{rel}: pinned but gone")
        elif want[rel] != got[rel]:
            a = {d["id"] for d in want[rel]["declarations"]}
            b = {d["id"] for d in got[rel]["declarations"]}
            if a != b:
                problems.append(f"{rel}: declarations changed: "
                                f"{sorted(a ^ b)}")
            else:
                for x, y in zip(want[rel]["declarations"],
                                got[rel]["declarations"]):
                    for key in sorted(set(x) | set(y)):
                        if x.get(key) != y.get(key):
                            problems.append(
                                f"{rel}: {x['id']}.{key}: "
                                f"{x.get(key)!r} -> {y.get(key)!r}")
    return problems


def main(argv) -> int:
    if "--write" in argv:
        GOLDEN.parent.mkdir(exist_ok=True)
        data = generate()
        GOLDEN.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
        n = sum(len(v["declarations"]) for v in data.values())
        print(f"wrote {GOLDEN.relative_to(ROOT)}: {len(data)} file(s), "
              f"{n} declaration(s)")
        return 0
    problems = compare()
    for p in problems:
        print("  ", p)
    print("props golden: OK" if not problems
          else f"props golden: {len(problems)} differ")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
