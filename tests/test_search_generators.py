"""The generators, and the guards that stop them wasting the search.

These are the functions that actually find defects: small-scope enumeration
over the shapes a rule can distinguish, and one-step mutations of a world
where something already holds. Every path tested here is a *guard* — the
branch that declines to produce a candidate — and a guard that silently
stops guarding does not fail anything. It makes the search slower, or
noisier, or unbounded, and the counterexamples still look fine.

Each was unexercised when this file was written, measured at 94% over
`generators.py` with exactly these seven lines missing.

    python3 tests/test_search_generators.py
"""

from __future__ import annotations

import copy
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tests"),
                str(ROOT / "tests" / "fixtures")]

from attest import rulec                                          # noqa: E402
from attest.search.cx.generators import (                         # noqa: E402
    MUTATORS,
    _foreign_subject,
    _retract,
    future_dated,
    mutants,
    small_scope,
)
from attest.search.cx.world_set import WorldSet                   # noqa: E402

import schema_offline                                             # noqa: E402

RULES = ROOT / "tests" / "fixtures" / "rules"

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


def model():
    return schema_offline.model(ROOT / "tests" / "fixtures" / "schema.tql")


def band_rule(name: str = "latest-high"):
    return rulec.load(str(RULES / f"{name}.rule"))


def unscoped(rule):
    """The same rule with the `via` role dropped from every collection."""
    out = copy.deepcopy(rule)
    for c in out["collections"]:
        c.pop("via", None)
        c.pop("scope", None)
    return out


def a_world(**over):
    row = {"holder": "s1", "test-code": "alpha", "amount": 95,
           "taken-day": 19900, "fact-id": "f001", "source": "feed",
           "recorded-at": "2026-01-01T00:00:00", "retracted-at": None}
    row.update(over)
    return WorldSet(data={"readings": [row]})


@check("a rule with no collections yields no small-scope worlds")
def _():
    # Enumerating over nothing used to fall through to the row loop and
    # yield one empty world per collection — of which there are none — so
    # the behaviour was right by accident. A rule reading only parameters
    # has nothing to enumerate and must say so.
    bare = copy.deepcopy(band_rule())
    bare["collections"] = []
    got = list(small_scope({"bare": bare}, model(), max_rows=2))
    assert got == [], f"{len(got)} worlds from a rule with no collections"


@check("small scope stops at its limit")
def _():
    # The limit is what keeps the search bounded; `max_rows` alone does not,
    # because the row set grows with the partitioned field values. Without
    # it a wide rule enumerates until the process is killed.
    rules = {"latest-high": band_rule()}
    unbounded = list(small_scope(rules, model(), max_rows=2, limit=20000))
    assert len(unbounded) > 12, (
        f"only {len(unbounded)} worlds, so the limit below proves nothing")
    for limit in (1, 5, 12):
        got = list(small_scope(rules, model(), max_rows=2, limit=limit))
        assert len(got) == limit, (
            f"limit {limit} produced {len(got)} worlds")


@check("the via role is pinned to the subject only where the rule scopes it")
def _():
    # `_scope_fields` overrides the partitioned value of the `via` role with
    # the subject, so every scoped row is the subject's own. For a
    # collection with no `via` it returns {} and the role keeps whatever the
    # partition drew. Pinning it for an unscoped collection would make every
    # world the subject's, and a rule that forgot to check whose record it
    # is would then look correct — which is exactly the defect the
    # foreign-subject mutator exists to find.
    m = model()
    scoped = list(small_scope({"s": band_rule()}, m, max_rows=1, limit=6))
    seen = {row.get("holder") for c in scoped for row in c.ws.data["readings"]}
    assert seen == {"s1"}, f"a scoped row was not the subject's: {seen}"

    plain = list(small_scope({"u": unscoped(band_rule())}, m,
                             max_rows=1, limit=6))
    assert plain, "no worlds at all"
    seen = {row.get("holder") for c in plain for row in c.ws.data["readings"]}
    assert "s1" not in seen, f"an unscoped row was pinned to the subject: {seen}"


@check("the foreign-subject mutator declines a collection it cannot scope")
def _():
    # Nothing to make foreign: there is no role saying whose row it is. The
    # mutator must decline rather than return the world unchanged, which
    # would be screened as a candidate and spend a kernel confirmation on a
    # world identical to one already seen.
    rule = unscoped(band_rule())
    ws = a_world()
    assert _foreign_subject(ws, "readings", ws.data["readings"][0], rule) is None

    # and a scoped collection whose row happens to carry no subject
    scoped = band_rule()
    bare = a_world(holder=None)
    assert _foreign_subject(bare, "readings", bare.data["readings"][0], scoped) is None

    # the positive case, so the two refusals above are not vacuous
    ws = a_world()
    made = _foreign_subject(ws, "readings", ws.data["readings"][0], scoped)
    assert made is not None, "a scoped row could not be made foreign"
    out, origin = made
    assert out.data["readings"][0]["holder"] == "someone-else", out.data
    assert origin["mutator"] == "foreign-subject", origin
    assert ws.data["readings"][0]["holder"] == "s1", "the input was mutated"


@check("the retract mutator declines a row that is already retracted")
def _():
    # Retracting twice is a world the store refuses, so the candidate would
    # be thrown away by tier 1 after being built and screened. More
    # importantly it is the shape of a real defect the suite checks for
    # elsewhere, and the generator must not manufacture it.
    rule = band_rule()
    pulled = a_world(**{"retracted-at": "2026-03-01T00:00:00"})
    assert _retract(pulled, "readings", pulled.data["readings"][0], rule) is None

    live = a_world()
    made = _retract(live, "readings", live.data["readings"][0], rule)
    assert made is not None, "a live row could not be retracted"
    out, origin = made
    assert out.data["readings"][0]["retracted-at"], out.data
    assert origin["mutator"] == "retract", origin
    assert live.data["readings"][0]["retracted-at"] is None, "input was mutated"


@check("mutants skips the mutators that decline, and keeps the rest")
def _():
    # One declining mutator must not end the loop or drop the others.
    rule = unscoped(band_rule())          # foreign-subject will decline
    ws = a_world(**{"retracted-at": "2026-03-01T00:00:00"})  # retract too
    got = list(mutants(ws, {"u": rule}))
    kinds = sorted(c.origin["mutator"] for c in got)
    assert kinds == ["duplicate"], (
        f"expected only the duplicate mutator to apply, got {kinds}")
    # all three apply to a live, scoped row
    both = list(mutants(a_world(), {"s": band_rule()}))
    assert sorted(c.origin["mutator"] for c in both) == [
        "duplicate", "foreign-subject", "retract"], [
            c.origin["mutator"] for c in both]
    assert len(MUTATORS) == 3, f"{len(MUTATORS)} mutators now exist"
    for cand in both:
        assert cand.before is ws or cand.before is not None, (
            "a mutant carries no before-world, so no change property can "
            "read it")


@check("future-dated skips a collection the world does not have")
def _():
    # It copies row 0 as its template, so an absent or empty collection has
    # nothing to copy. Indexing it would raise inside the generator and end
    # the whole search, not just this candidate.
    rule = band_rule()
    assert list(future_dated(WorldSet(data={}), {"r": rule})) == []
    assert list(future_dated(WorldSet(data={"readings": []}), {"r": rule})) == []

    got = list(future_dated(a_world(), {"r": rule}))
    assert got, "no future-dated candidate from a world with a row"
    for cand in got:
        added = [r for r in cand.ws.data["readings"]
                 if r["taken-day"] > cand.ws.as_of_day]
        assert added, f"nothing dated after the decision: {cand.ws.data}"
        assert cand.before is not None, "no before-world"


@check("a row's date is the attribute the rules compare with as-of-day")
def _():
    # Read from the rules, not assumed: this fixture's date is `taken-day`.
    # The generator used to write the literal `effective-day`, one domain's
    # name for it, so everywhere else its "future" row was the old row with
    # an extra key nothing read.
    from attest.search.cx.generators import day_attributes
    rule = band_rule()
    assert day_attributes({"r": rule}, "readings") == ["taken-day"], \
        day_attributes({"r": rule}, "readings")
    assert day_attributes({"r": rule}, "nothing-here") == []
    for cand in future_dated(a_world(), {"r": rule}):
        new = [r for r in cand.ws.data["readings"]
               if r["fact-id"].startswith("future-")]
        assert new and all("effective-day" not in r for r in new), new


if __name__ == "__main__":
    for name in PASS:
        print(f"  pass  {name}")
    for name, why in FAIL:
        print(f"  FAIL  {name}\n          {why}")
    print(f"\n{len(PASS)}/{len(PASS) + len(FAIL)} passed")
    sys.exit(1 if FAIL else 0)
