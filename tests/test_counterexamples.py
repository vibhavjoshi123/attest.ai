"""The counterexample search, against the defects it was built to find.

Four defects were found by two kernel audits in `d0fbabb`, none of which
any live run could have caught. This suite asks whether a search finds
them unaided — and, just as importantly, whether it stays quiet on the
rules as they stand today. A searcher that cries wolf on correct rules is
worse than none, because people stop reading it.

Three of the four are fixture RULE-TEXT defects, reproduced here from the
texts before the fix:

1. a same-day tie made both band branches fire at once;
2. the first fix for (1) was worse — a tie-break on `fact-id !=` silenced
   the branch for two identical results from two feeds;
3. no upper bound on `taken-day`, so a reading dated after the decision
   won "latest".

The fourth kind is a SCHEMA defect — a world the schema forbids, such as
a value outside an attribute's `@values` — and it is not reachable by
searching snapshots of a rule: the store refuses such a world outright. The right question for it is whether the Guide rejects that
world as impossible rather than reporting a defect about a state nothing
can reach, which is what `defect 4` below checks.

    python3 tests/test_counterexamples.py
"""

from __future__ import annotations

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tests"), str(ROOT / "examples")]

from attest import rulec                                          # noqa: E402
from attest.props import parse_family, validate                   # noqa: E402
from attest.search.cx import guide, search as cx                   # noqa: E402
from attest.search.cx.world_set import WorldSet                    # noqa: E402

import schema_offline                                              # noqa: E402

RULES = ROOT / "tests" / "fixtures" / "rules"
MUTANTS = pathlib.Path(__file__).resolve().parent / "mutants" / "fixture"
FIXTURES = pathlib.Path(__file__).resolve().parent / "counterexamples"
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


def _model():
    return schema_offline.model(ROOT / "tests" / "fixtures" / "schema.tql")


def _decl(prop_id: str):
    decls = [d for f in RULES.glob("*.family")
             for d in parse_family(f.read_text())]
    validate(decls, {p.stem for p in RULES.glob("*.rule")})
    found = [d for d in decls if d.id == prop_id]
    assert found, f"no declaration {prop_id}; have {[d.id for d in decls]}"
    return found[0]


def _rules(pattern: str, names=BAND):
    return {n: rulec.load(str(pattern).format(n)) for n in names}


FIXED = str(RULES / "{}.rule")
HISTORICAL = str(MUTANTS / "historical-{}.rule")
DEFECT2 = str(MUTANTS / "defect2-{}.rule")


def _verdicts(world: dict, rules: dict, model) -> dict:
    return WorldSet(data=world["data"], subject=world["subject"],
                    as_of_day=world["as_of_day"]).verdicts(rules, model)


def _search(prop_id, pattern, **kw):
    kw.setdefault("max_rows", 2)
    kw.setdefault("limit", 4000)
    kw.setdefault("stop_after", 3)
    return cx.search(_decl(prop_id), _rules(pattern), _model(), **kw)


@check("defect 1: a same-day tie is found, and firing both branches at once")
def _():
    found = _search("fixture.alpha-band.exclusive", HISTORICAL)
    assert found, "the same-day tie was not rediscovered"
    v = found[0]
    assert all(v.verdicts[r] for r in BAND), v.verdicts
    rows = v.world["data"]["readings"]
    assert len(rows) <= 2, f"not shrunk: {len(rows)} rows"
    days = {r["taken-day"] for r in rows}
    assert len(days) == 1, f"the defect is a TIE; days were {days}"
    values = {r["amount"] for r in rows}
    assert len(values) == 2, f"a tie needs two different readings: {values}"


@check("defect 2: an exact duplicate silencing a branch is found")
def _():
    found = _search("fixture.reingestion.stable-add", DEFECT2, max_rows=1,
                    limit=3000)
    assert found, "the re-ingestion defect was not rediscovered"
    v = found[0]
    assert v.verdicts != v.verdicts_after, (v.verdicts, v.verdicts_after)
    assert v.origin.get("mutator") == "duplicate", v.origin


@check("defect 3: a reading dated after the decision changing a verdict is found")
def _():
    found = _search("fixture.alpha-band.stable-add", HISTORICAL, max_rows=1,
                    limit=2000)
    assert found, "the future-dated defect was not rediscovered"
    v = found[0]
    assert v.verdicts != v.verdicts_after, (v.verdicts, v.verdicts_after)
    added = [r for r in v.world["data"]["readings"]
             if r["taken-day"] > v.world["as_of_day"]]
    assert added, "no row was dated after the decision"


@check("tier 1 rejects a row with no fact-id, and a missing collection")
def _():
    # Both are worlds the store cannot hold, and both were unexercised. A
    # row with no fact-id cannot be retracted or relied on, and a
    # collection the rules read but the world lacks makes every `some` over
    # it vacuously false — so the world says nothing, and any "violation"
    # found on it is an artefact of the gap rather than a defect.
    model, rules = _model(), _rules(FIXED)
    row = {"holder": "s1", "test-code": "alpha", "amount": 95,
           "taken-day": 19900, "source": "feed",
           "recorded-at": "2026-06-01T00:00:00", "retracted-at": None}
    anonymous = WorldSet(data={"readings": [dict(row)]})      # no fact-id
    why = guide.well_formed(anonymous, model, rules)
    assert any("no fact-id" in w for w in why), why

    # every rule here reads `readings`; a world without it is not well formed
    empty = WorldSet(data={})
    why = guide.well_formed(empty, model, rules)
    assert any("which this world lacks" in w for w in why), why
    assert any("readings" in w for w in why), why


@check("tier 2 ranks a repeated reading and a retraction above a plain world")
def _():
    # The Guide never deletes a candidate on tier 2; it ranks. Both of
    # these shapes are what the historical defects looked like, so a world
    # carrying one must sort above an ordinary one or the search reaches it
    # late or not at all within its budget.
    model, rules = _model(), _rules(FIXED)
    base = {"holder": "s1", "test-code": "alpha", "amount": 95,
            "taken-day": 19900, "source": "feed",
            "recorded-at": "2026-06-01T00:00:00", "retracted-at": None}
    plain = WorldSet(data={"readings": [dict(base, **{"fact-id": "f1"})]})
    twice = WorldSet(data={"readings": [dict(base, **{"fact-id": "f1"}),
                                    dict(base, **{"fact-id": "f2"})]})
    pulled = WorldSet(data={"readings": [
        dict(base, **{"fact-id": "f1",
                      "retracted-at": "2026-07-01T00:00:00"})]})
    score = lambda ws: guide.interesting(ws, model, rules)      # noqa: E731
    assert score(twice) > score(plain), (score(twice), score(plain))
    assert score(pulled) > score(plain), (score(pulled), score(plain))

    # A same-day pair with DIFFERENT values is ranked as a tie only because
    # the rules say `taken-day` is this collection's date. The ranking used
    # to read the literal `effective-day`, one domain's name for it, and
    # scored this world exactly like a plain one.
    tie = WorldSet(data={"readings": [
        dict(base, **{"fact-id": "f1"}),
        dict(base, **{"fact-id": "f2", "amount": 60})]})
    other = WorldSet(data={"readings": [
        dict(base, **{"fact-id": "f1"}),
        dict(base, **{"fact-id": "f2", "amount": 60, "taken-day": 19800})]})
    assert score(tie) > score(other), (score(tie), score(other))


@check("defect 4: a world the store cannot hold is rejected, not reported")
def _():
    # The fourth kind of defect is a schema one: a world the store refuses,
    # here a test code outside `@values`. A search over snapshots must not report defects about states
    # the store refuses — it would be describing something nobody can
    # reach. Tier 1 is what keeps that out.
    model = _model()
    rules = _rules(FIXED)
    impossible = WorldSet(data={"readings": [
        {"holder": "s1", "test-code": "NOT-A-CODE", "amount": 95,
         "taken-day": 19900, "fact-id": "f001", "source": "feed",
         "recorded-at": "2026-01-01T00:00:00", "retracted-at": None}]})
    why = guide.well_formed(impossible, model, rules)
    assert why, "a value outside @values was admitted"
    assert "outside @values" in " ".join(why), why
    # and the ordinary ones are admitted
    fine = WorldSet(data={"readings": [
        {"holder": "s1", "test-code": "alpha", "amount": 95,
         "taken-day": 19900, "fact-id": "f001", "source": "feed",
         "recorded-at": "2026-01-01T00:00:00", "retracted-at": None}]})
    assert guide.well_formed(fine, model, rules) == [], \
        guide.well_formed(fine, model, rules)


@check("a duplicate fact-id and a backwards retraction are both rejected")
def _():
    model, rules = _model(), _rules(FIXED)
    row = {"holder": "s1", "test-code": "alpha", "amount": 95,
           "taken-day": 19900, "source": "feed",
           "recorded-at": "2026-06-01T00:00:00", "retracted-at": None}
    twice = WorldSet(data={"readings": [dict(row, **{"fact-id": "f001"}),
                                    dict(row, **{"fact-id": "f001"})]})
    assert any("appears in" in w for w in
               guide.well_formed(twice, model, rules))
    backwards = WorldSet(data={"readings": [
        dict(row, **{"fact-id": "f001",
                     "retracted-at": "2026-01-01T00:00:00"})]})
    assert any("before" in w for w in
               guide.well_formed(backwards, model, rules))


@check("today's rules violate none of the declared properties")
def _():
    # The regression direction, and the one that matters most day to day.
    for prop_id, kw in (("fixture.alpha-band.exclusive", {}),
                        ("fixture.alpha-band.stable-add",
                         {"max_rows": 1, "limit": 2000}),
                        ("fixture.reingestion.stable-add",
                         {"max_rows": 1, "limit": 3000})):
        found = _search(prop_id, FIXED, **kw)
        assert not found, (
            f"{prop_id}: {len(found)} violation(s) of a property today's "
            f"rules are supposed to satisfy — first: "
            f"{found[0].verdicts} -> {found[0].verdicts_after}")


@check("a violation shrinks to at most two rows per collection")
def _():
    found = _search("fixture.alpha-band.exclusive", HISTORICAL)
    assert found
    for v in found:
        for coll, rows in v.world["data"].items():
            assert len(rows) <= 2, f"{coll} kept {len(rows)} rows"


@check("the same defect found twice is reported once")
def _():
    found = _search("fixture.alpha-band.exclusive", HISTORICAL, limit=8000,
                    stop_after=8)
    sigs = [v.signature for v in found]
    assert len(sigs) == len(set(sigs)), sigs


@check("every committed fixture still violates its property")
def _():
    from attest.search.cx.props_eval import predicate

    files = sorted(FIXTURES.rglob("*.json"))
    # An empty directory used to `return` here, so this check passed without
    # checking anything — coverage that was not coverage. The fixtures are
    # written by `tests/make_counterexamples.py --write`, which only writes
    # one the kernel has confirmed, so their absence is a failure.
    assert files, ("no counterexample fixtures committed: run "
                   "`python3 tests/make_counterexamples.py --write`")
    model = _model()
    for path in files:
        data = json.loads(path.read_text())
        decl = _decl(data["property"])
        rules = _rules(str(ROOT / data["rules_pattern"]))
        holds = predicate(decl)

        # `world` is the world the property is evaluated AT: for a change
        # property that is the world AFTER the change, and `verdicts` are the
        # verdicts BEFORE it. Checking `verdicts` against `world` compares
        # two different worlds — the mistake `confirm` made until defects 2
        # and 3 came back refuted — so each reading is rebuilt with its own
        # verdicts.
        after = _verdicts(data["world"], rules, model)
        if data["verdicts_after"] is None:
            assert after == data["verdicts"], (
                f"{path.name}: verdicts moved: {after} != {data['verdicts']}")
            assert not holds(after), f"{path.name}: no longer violates"
            continue
        assert data["before"], f"{path.name}: a change fixture with no before"
        before = _verdicts(data["before"], rules, model)
        assert before == data["verdicts"], (
            f"{path.name}: before verdicts moved: {before} != "
            f"{data['verdicts']}")
        assert after == data["verdicts_after"], (
            f"{path.name}: after verdicts moved: {after} != "
            f"{data['verdicts_after']}")
        assert not holds(before, after), f"{path.name}: no longer violates"


def _claimed(verdicts, verdicts_after=None):
    world = {"data": {}, "subject": "p", "as_of_day": 0}
    return cx.Violation(
        decl_id="x", kind="change" if verdicts_after is not None else "state",
        world=world, before=world if verdicts_after is not None else None,
        verdicts=verdicts, verdicts_after=verdicts_after,
        signature="s", origin={})


class _NoKernel:
    """Fails the test if anything reaches it: these violations are refused
    before a single check is spent."""
    def __getattr__(self, name):
        raise AssertionError(f"the kernel was asked ({name})")


@check("a violation whose verdicts match no rule is not confirmed")
def _():
    # `all()` over the checks that ran is True when none ran, so this came
    # back confirmed having asked the kernel nothing.
    report = cx.confirm(_claimed({"latest-high": True}), {}, None,
                        _NoKernel(), _NoKernel())
    assert report["_confirmed"] is False, report
    assert report["_unchecked"] == ["latest-high"], report


@check("a change read on one side only is not confirmed")
def _():
    # The claim is that a verdict MOVED; a rule with a reading on one side
    # of the change has nothing to have moved from.
    rules = {"latest-high": object(), "latest-low": object()}
    report = cx.confirm(
        _claimed({"latest-high": True, "latest-low": False},
                 {"latest-high": False}),
        rules, None, _NoKernel(), _NoKernel())
    assert report["_confirmed"] is False, report
    assert report["_unchecked"] == [
        "latest-low (read on one side of the change only)"], report


@check("a change whose after-verdict names no rule is not confirmed")
def _():
    # The before side matches a rule, so a check would run there; the after
    # side names a rule nobody passed. The old code checked the half it
    # could and reported the whole claim confirmed.
    rules = {"latest-high": object()}
    report = cx.confirm(
        _claimed({"latest-high": True},
                 {"latest-high": False, "renamed-rule": True}),
        rules, None, _NoKernel(), _NoKernel())
    assert report["_confirmed"] is False, report
    assert "renamed-rule@after" in report["_unchecked"], report


@check("a fully claimed violation still reaches the kernel")
def _():
    # The guard must refuse only what it cannot check, never a complete
    # claim: a violation whose every verdict names a passed rule goes on to
    # the checks. The placeholder rule cannot be compiled, so getting past
    # the guard raises; an early `_confirmed: False` return would not.
    rules = {"latest-high": object()}
    try:
        cx.confirm(_claimed({"latest-high": True}), rules, None,
                   _NoKernel(), _NoKernel())
    except Exception:                                          # noqa: BLE001
        return
    raise AssertionError("a complete claim was refused without a check")


if __name__ == "__main__":
    for name in PASS:
        print(f"  pass  {name}")
    for name, why in FAIL:
        print(f"  FAIL  {name}\n          {why}")
    print(f"\n{len(PASS)}/{len(PASS) + len(FAIL)} passed")
    sys.exit(1 if FAIL else 0)
