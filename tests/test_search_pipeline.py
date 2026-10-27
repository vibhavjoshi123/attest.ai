"""The search pipeline's own joints, offline.

`test_counterexamples.py` drives the whole search and checks what it finds.
This checks the pieces it is assembled from, and in particular the paths no
shipped declaration reaches:

  - `stable-retract` has no declaration in `tests/fixtures/rules/`, so
    neither its in-scope test nor its generator ran. A kind that compiles
    and is never exercised is a kind that will be wrong the day someone
    declares one.
  - `_readings` splits a change property into a before and an after; offline
    nothing called it, because `confirm` needs Lean.
  - the guards that decline a candidate — no before-world, a reading that
    raises, a shrink that loses the violation — none of which fails
    anything when it stops working. The search just reports less, or
    reports nonsense.

    python3 tests/test_search_pipeline.py
"""

from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tests"),
                str(ROOT / "tests" / "fixtures")]

from attest import rulec                                          # noqa: E402
from attest.props import PropertyDecl                             # noqa: E402
from attest.search.cx.generators import Candidate                 # noqa: E402
from attest.search.cx.search import (                             # noqa: E402
    Violation,
    _change_in_scope,
    _readings,
    candidates,
    confirm,
    screen,
    search,
    signature,
)
from attest.search.cx.world_set import DUPLICATE, WorldSet        # noqa: E402

import schema_offline                                             # noqa: E402

RULES = ROOT / "tests" / "fixtures" / "rules"
BAND = ("latest-high", "latest-low")

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


def rules():
    return {n: rulec.load(str(RULES / f"{n}.rule")) for n in BAND}


def row(**over):
    base = {"holder": "s1", "test-code": "alpha", "amount": 95,
            "taken-day": 19900, "fact-id": "f001", "source": "feed",
            "recorded-at": "2026-01-01T00:00:00", "retracted-at": None}
    base.update(over)
    return base


def world(*rows, as_of_day: int = 19950):
    return WorldSet(data={"readings": list(rows)}, subject="s1",
                    as_of_day=as_of_day)


ADD = PropertyDecl(id="d.add", kind="stable-add", rules=BAND,
                   collections=("readings",), when="taken-day > as-of-day")
RETRACT = PropertyDecl(id="d.ret", kind="stable-retract", rules=BAND,
                       collections=("readings",),
                       when="taken-day > as-of-day")


@check("a change property with no before-world is declined, not read")
def _():
    # `screen` would otherwise call `.verdicts` on None, and
    # `_change_in_scope` would compare against nothing. Both must decline:
    # a candidate with no before cannot show that anything moved.
    cand = Candidate(ws=world(row()), origin={"generator": "small-scope"})
    assert cand.before is None
    violated, verdicts, after = screen(cand, ADD, rules(), model())
    assert violated is False and verdicts == {} and after is None, (
        violated, verdicts, after)
    assert _change_in_scope(cand, ADD) is False


@check("stable-retract is in scope for a retraction, and not for an addition")
def _():
    # No shipped declaration is a `stable-retract`, so this branch had never
    # run. It must answer about RETRACTIONS: a row pulled after the decision
    # is the change the claim is about, while a row merely added is the
    # other kind of claim entirely.
    before = world(row())
    pulled = world(row(**{"retracted-at": "2026-07-01T00:00:00",
                          "taken-day": 19990}))
    cand = Candidate(ws=pulled, before=before,
                     origin={"generator": "mutator", "mutator": "retract"})
    assert _change_in_scope(cand, RETRACT) is True, "a retraction is in scope"

    # the same world with the row still live is not a retraction at all
    live = world(row(**{"taken-day": 19990}))
    assert _change_in_scope(
        Candidate(ws=live, before=before, origin={}), RETRACT) is False, (
        "a live row was read as a retraction")

    # and the `when` filter still applies: a row retracted but dated BEFORE
    # the decision is not the row this declaration speaks about
    early = world(row(**{"retracted-at": "2026-07-01T00:00:00",
                         "taken-day": 19800}))
    assert _change_in_scope(
        Candidate(ws=early, before=before, origin={}), RETRACT) is False, (
        "the when filter was ignored on the retraction branch")


@check("the when filter applies to an added row, not only a retracted one")
def _():
    # `_change_in_scope` has two loops with a `when` test in each: one over
    # rows that are NEW, one over rows that were RETRACTED. Only the
    # retraction branch was tested, so the addition branch could stop
    # filtering entirely and every suite stayed green — while the search
    # reported every correct rule as broken, because a row dated BEFORE the
    # decision is exactly the row a working rule is supposed to react to.
    before = world(row())
    after = Candidate(ws=world(row(), row(**{"fact-id": "f002",
                                             "taken-day": 19990})),
                      before=before, origin={})
    assert _change_in_scope(after, ADD) is True, (
        "a row added after the decision is the change this claim is about")

    early = Candidate(ws=world(row(), row(**{"fact-id": "f003",
                                             "taken-day": 19800})),
                      before=before, origin={})
    assert _change_in_scope(early, ADD) is False, (
        "the when filter was ignored on the addition branch: a row dated "
        "before the decision was read as the change")

    # a collection the declaration does not name is out of scope whatever
    # its rows are dated
    other = PropertyDecl(id="d.other", kind="stable-add", rules=BAND,
                         collections=("ledger",),
                         when="taken-day > as-of-day")
    assert _change_in_scope(after, other) is False, (
        "a change to a collection the declaration does not name")


@check("a duplicate reading is in scope; a different reading is not")
def _():
    # `when duplicate` is not a comparison, it is "this row says the same
    # thing as one already there" — the second historical defect, where a
    # tie-break on `fact-id !=` silenced a branch for two identical results
    # arriving from two feeds. The branch that recognises it had no test.
    dup = PropertyDecl(id="d.dup", kind="stable-add", rules=BAND,
                       collections=("readings",), when=DUPLICATE)
    before = world(row())
    same = Candidate(ws=world(row(), row(**{"fact-id": "f002"})),
                     before=before, origin={})
    assert _change_in_scope(same, dup) is True, (
        "a second row with the same reading is a duplicate")

    differs = Candidate(ws=world(row(), row(**{"fact-id": "f002",
                                               "amount": 60})),
                        before=before, origin={})
    assert _change_in_scope(differs, dup) is False, (
        "a row with a different reading was called a duplicate")

    # the duplicate branch must not fall through to the comparison branch:
    # `duplicate` is not an operator, and reading it as one raises
    unchanged = Candidate(ws=world(row()), before=before, origin={})
    assert _change_in_scope(unchanged, dup) is False


@check("a violation the kernel was never asked about is not confirmed")
def _():
    # `all()` over an empty sequence is True, so a violation that produced
    # no checks at all was reported CONFIRMED — kernel-confirmed, with no
    # kernel involved. The guard is `bool(checks)`, and it was reachable
    # only through a fixture that happened to have verdicts, which every
    # committed one does.
    #
    # Nothing here needs Lean: with no verdicts to read there is nothing to
    # ask, which is the whole point.
    empty = Violation(
        decl_id="d.x", kind="exclusive",
        world={"data": {"readings": [row()]}, "subject": "s1",
               "as_of_day": 19950},
        before=None, verdicts={}, verdicts_after=None,
        signature="s", origin={})
    out = confirm(empty, rules(), model(), lean=None, kernel=None)
    assert out["_confirmed"] is False, (
        f"confirmed with no checks at all: {out}")
    assert [k for k in out if not k.startswith("_")] == [], out

    # the same violation naming a rule nobody passed in is unconfirmable,
    # and says which rule it could not read
    unknown = Violation(
        decl_id="d.x", kind="exclusive",
        world=empty.world, before=None,
        verdicts={"not-a-rule": True}, verdicts_after=None,
        signature="s", origin={})
    out = confirm(unknown, rules(), model(), lean=None, kernel=None)
    assert out["_confirmed"] is False and out["_unchecked"] == ["not-a-rule"]


@check("stable-retract asks only for retract mutants")
def _():
    # `candidates` branches on the kind: `stable-add` gets future-dated rows
    # and duplicates, `stable-retract` gets retractions. Feeding one the
    # other's candidates is what reported a correct rule as broken once
    # already.
    rs, m = rules(), model()
    got = list(candidates(RETRACT, rs, m, max_rows=1, limit=40))
    assert got, "no candidates at all"
    kinds = {c.origin.get("mutator") for c in got}
    assert kinds == {"retract"}, f"stable-retract was fed {kinds}"
    for c in got:
        assert c.before is not None, "a change candidate with no before"

    adds = {c.origin.get("mutator") for c in
            candidates(ADD, rs, m, max_rows=1, limit=40)}
    assert "retract" not in adds, f"stable-add was fed a retraction: {adds}"


@check("a non-change violation has one reading; a change has before and after")
def _():
    # The readings are what `confirm` asks the kernel about. Getting the
    # split wrong is how `confirm` came to pair the world AFTER a change
    # with the verdicts BEFORE it.
    plain = Violation(
        decl_id="d.x", kind="exclusive",
        world={"data": {"readings": [row()]}, "subject": "s1",
               "as_of_day": 19950},
        before=None, verdicts={"latest-high": True}, verdicts_after=None,
        signature="s", origin={})
    got = _readings(plain)
    assert len(got) == 1, got
    label, w, v = got[0]
    assert label == "" and w is plain.world and v is plain.verdicts

    changed = Violation(
        decl_id="d.add", kind="stable-add",
        world={"data": {"readings": [row(), row(**{"fact-id": "f002"})]},
               "subject": "s1", "as_of_day": 19950},
        before={"data": {"readings": [row()]}, "subject": "s1",
                "as_of_day": 19950},
        verdicts={"latest-high": True}, verdicts_after={"latest-high": False},
        signature="s", origin={})
    got = _readings(changed)
    assert [label for label, _w, _v in got] == ["@before", "@after"], got
    (_lb, wb, vb), (_la, wa, va) = got
    assert wb["data"] == changed.before["data"], "the before world is wrong"
    assert wa is changed.world, "the after world is wrong"
    assert vb is changed.verdicts and va is changed.verdicts_after
    assert len(wb["data"]["readings"]) == 1 and len(wa["data"]["readings"]) == 2, (
        "the two readings describe the same world, so nothing moved")


@check("a change violation that lost its before-world still reads")
def _():
    # `before or world` is the fallback. A violation stored without its
    # before-world would otherwise crash `confirm` on a None subscript
    # rather than simply confirming nothing useful.
    changed = Violation(
        decl_id="d.add", kind="stable-add",
        world={"data": {"readings": [row()]}, "subject": "s1",
               "as_of_day": 19950},
        before=None,
        verdicts={"latest-high": True}, verdicts_after={"latest-high": True},
        signature="s", origin={})
    got = _readings(changed)
    assert [label for label, _w, _v in got] == ["@before", "@after"], got
    assert got[0][1]["subject"] == "s1", got[0][1]
    assert got[0][1]["as_of_day"] == 19950, got[0][1]

    # a before-world carrying only `data` borrows the rest from the after
    partial = Violation(
        decl_id="d.add", kind="stable-add",
        world={"data": {"readings": [row()]}, "subject": "s9",
               "as_of_day": 20100},
        before={"data": {"readings": []}},
        verdicts={"latest-high": False}, verdicts_after={"latest-high": True},
        signature="s", origin={})
    label, w, _v = _readings(partial)[0]
    assert (w["subject"], w["as_of_day"]) == ("s9", 20100), w


@check("a violation serialises with every field a fixture needs")
def _():
    # `as_dict` is how a counterexample becomes a committed fixture, and it
    # ran only when fixtures were regenerated.
    v = Violation(
        decl_id="d.x", kind="exclusive",
        world={"data": {"readings": [row()]}, "subject": "s1",
               "as_of_day": 19950},
        before=None, verdicts={"latest-high": True, "latest-low": True},
        verdicts_after=None, signature="abc123", origin={"generator": "g"},
        shrink_log=["dropped readings f002"], rank=3)
    d = v.as_dict()
    assert d["property"] == "d.x" and d["kind"] == "exclusive"
    assert d["signature"] == "abc123" and d["rank"] == 3
    assert d["verdicts"] == {"latest-high": True, "latest-low": True}
    assert d["verdicts_after"] is None and d["before"] is None
    assert d["shrink_log"] == ["dropped readings f002"]
    assert d["kernel"] == {}, d["kernel"]
    # the replay reads these five by name; a rename must fail here
    for key in ("property", "world", "verdicts", "verdicts_after",
                "signature"):
        assert key in d, f"a fixture could not be written without {key}"
    import json
    json.dumps(d)                      # a fixture is JSON on disk


@check("search reports its progress and stops where it is told")
def _():
    # `on_candidate` is how a long run says where it is. It is called once
    # per candidate looked at, with a running count, and nothing else called
    # it — a run with no progress at all is indistinguishable from a hung
    # one.
    seen = []
    decl = PropertyDecl(id="fixture.alpha-band.exclusive", kind="exclusive",
                        rules=BAND)
    found = search(decl, rules(), model(), max_rows=1, limit=60,
                   stop_after=1, on_candidate=seen.append)
    assert seen, "on_candidate was never called"
    assert seen == sorted(seen), "the count went backwards"
    assert seen == list(range(1, len(seen) + 1)), (
        f"the count is not one per candidate: {seen[:6]}…")
    # today's rules satisfy the property, so a bounded run finds nothing and
    # must still have looked
    assert found == [], f"the shipped rules violate exclusivity: {found}"
    assert len(seen) > 1, f"only {len(seen)} candidate(s) examined"


@check("a reading that cannot be taken skips its candidate, not the search")
def _():
    # `predicate` raises rather than inventing a verdict for a rule it was
    # not given, which is right — a silent False would be reported as a
    # counterexample. `search` therefore has to skip that candidate and
    # carry on; letting the exception out would end the whole run on one
    # malformed declaration, and the run would look like "nothing found".
    decl = PropertyDecl(id="d.missing", kind="exclusive",
                        rules=("latest-high", "not-a-rule"))
    found = search(decl, rules(), model(), max_rows=1, limit=40, stop_after=2)
    assert found == [], f"a violation was reported anyway: {found}"


@check("two worlds that differ only in fact-ids share a signature")
def _():
    # The signature is what stops the same defect being reported once per
    # fact-id. It reads the shape, not the ids.
    m, rs = model(), rules()
    a = Candidate(ws=world(row(**{"fact-id": "f001"})), origin={})
    b = Candidate(ws=world(row(**{"fact-id": "zzz9"})), origin={})
    decl = PropertyDecl(id="d.x", kind="exclusive", rules=BAND)
    assert signature(a, decl, rs, m) == signature(b, decl, rs, m), (
        "the fact-id leaked into the signature")
    c = Candidate(ws=world(row(**{"amount": 60})), origin={})
    assert signature(a, decl, rs, m) != signature(c, decl, rs, m), (
        "a different reading got the same signature")


if __name__ == "__main__":
    for name in PASS:
        print(f"  pass  {name}")
    for name, why in FAIL:
        print(f"  FAIL  {name}\n          {why}")
    print(f"\n{len(PASS)}/{len(PASS) + len(FAIL)} passed")
    sys.exit(1 if FAIL else 0)
