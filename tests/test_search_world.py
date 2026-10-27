"""The shared generator is pinned, so a searcher's results stay comparable.

`attest/search/world.py` is the one module every searcher draws snapshots
from — the counterexample search, the property prover and the abduction CLI
all read a rule through it. Three things therefore have to hold, and none of
them is about any single searcher:

* the generator is deterministic for a given seed, or a counterexample
  committed as a fixture cannot be replayed;
* its first outputs do not move silently, because every pinned result in
  `tests/golden/` and every committed counterexample was drawn from them;
* the reference reading of a rule agrees with the Lean one, which
  `tests/test_lean_offline.py` checks against the real kernel.

This file covers the first two. It is the regression gate for the move out
of `tests/refeval.py`.

    python3 tests/test_search_world.py
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import random
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tests")]

from attest import rulec                                          # noqa: E402
from attest.search import world                                   # noqa: E402

import schema_offline                                              # noqa: E402

PINNED = pathlib.Path(__file__).resolve().parent / "golden" / "world.json"
#: how many of the generator's first draws are held still
CASES = 20

PASS, FAIL = [], []


def check(name):
    def wrap(fn):
        try:
            fn()
            PASS.append(name)
        except Exception as exc:                                  # noqa: BLE001
            FAIL.append((name, f"{type(exc).__name__}: {exc}"))
        return fn
    return wrap


def _rule_and_model():
    rule = rulec.load(ROOT / "tests" / "fixtures" / "rules" / "blocked.rule")
    model = schema_offline.model(ROOT / "tests" / "fixtures" / "schema.tql")
    return rule, model


def draws(count: int = CASES) -> list[dict]:
    """The generator's first `count` outputs, as comparable data."""
    rule, model = _rule_and_model()
    out = []
    for seed in range(count):
        case = world.random_case(rule, model, random.Random(seed), size=4)
        out.append({
            "seed": seed,
            "scopes": case.scopes,
            "as_of_day": case.as_of_day,
            "data": case.data,
            "witnesses": case.witnesses(),
        })
    return out


@check("the generator is deterministic for a given seed")
def _():
    rule, model = _rule_and_model()
    for seed in (0, 7, 19):
        a = world.random_case(rule, model, random.Random(seed), size=4)
        b = world.random_case(rule, model, random.Random(seed), size=4)
        assert a.data == b.data, f"seed {seed} drew two different snapshots"
        assert a.witnesses() == b.witnesses(), f"seed {seed}: witnesses differ"


@check("a different seed draws a different snapshot")
def _():
    # Not strictly guaranteed, but a generator that ignored its seed would
    # pass every other test here while making fixtures meaningless.
    rule, model = _rule_and_model()
    seen = {json.dumps(world.random_case(rule, model, random.Random(s),
                                         size=4).data, sort_keys=True)
            for s in range(CASES)}
    assert len(seen) > CASES // 2, (
        f"{CASES} seeds produced only {len(seen)} distinct snapshots")


@check("the first 20 generator outputs are unchanged")
def _():
    # Compared through JSON on BOTH sides. `witnesses()` returns tuples,
    # which JSON writes as arrays and reads back as lists, so a direct `==`
    # against the pinned file reported every draw as moved when nothing had.
    got = json.loads(json.dumps(draws()))
    assert PINNED.exists(), (
        f"{PINNED.relative_to(ROOT)} is missing; write it with "
        f"`python3 tests/test_search_world.py --write`")
    want = json.loads(PINNED.read_text())
    assert want["count"] == len(got), (
        f"pinned {want['count']} draws, generated {len(got)}")
    for a, b in zip(want["draws"], got):
        assert a == b, (
            f"seed {b['seed']}: the generator's output moved. Every pinned "
            f"result and every committed counterexample was drawn from "
            f"these, so this is a change in what the search explores, not a "
            f"formatting difference.")


@check("the reference evaluator reads a witness out of its own snapshot")
def _():
    # A witness that names facts the snapshot does not contain would make
    # every counterexample unreplayable.
    rule, model = _rule_and_model()
    found = 0
    for seed in range(60):
        case = world.random_case(rule, model, random.Random(seed), size=4)
        ids = {row["fact-id"] for rows in case.data.values() for row in rows}
        for witness in case.witnesses():
            found += 1
            assert set(witness) <= ids, (
                f"seed {seed}: witness {witness} names facts outside the "
                f"snapshot")
    assert found, "no witness was drawn in 60 seeds; the test proves nothing"


@check("refeval still re-exports the moved names")
def _():
    import refeval
    for name in ("Case", "random_case", "add", "drop", "AS_OF_RE"):
        assert getattr(refeval, name) is getattr(world, name), name


def main(argv) -> int:
    if "--write" in argv:
        PINNED.parent.mkdir(exist_ok=True)
        PINNED.write_text(json.dumps(
            {"count": CASES, "rule": "tests/fixtures/rules/blocked.rule",
             "draws": draws()}, indent=1, sort_keys=True) + "\n")
        body = PINNED.read_text()
        print(f"wrote {PINNED.relative_to(ROOT)}: {CASES} draws, "
              f"sha256 {hashlib.sha256(body.encode()).hexdigest()[:12]}")
        return 0
    for name in PASS:
        print(f"  pass  {name}")
    for name, why in FAIL:
        print(f"  FAIL  {name}\n          {why}")
    print(f"\n{len(PASS)}/{len(PASS) + len(FAIL)} passed")
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
