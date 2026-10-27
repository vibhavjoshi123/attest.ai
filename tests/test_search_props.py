"""Declarations, and the fast reading of them the search uses.

`attest/props.py` is trusted: what a property claims is whatever generates
it. `attest/search/cx/props_eval.py` is not — it is a microsecond reading
of the same declaration over verdicts, so the counterexample search can
screen millions of candidates before asking the kernel about any of them.

    python3 tests/test_search_props.py
"""

from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from attest.props import (                                        # noqa: E402
    FamilyError,
    PropertyDecl,
    parse_family,
    validate,
)
from attest.search.cx.props_eval import predicate                 # noqa: E402
from attest.search.cx.world_set import (                          # noqa: E402
    DUPLICATE,
    WorldSet,
    matches_when,
)

RULES = ROOT / "tests" / "fixtures" / "rules"
MUST_FAIL = pathlib.Path(__file__).resolve().parent / "must_fail" / "family"

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


@check("the shipped fixture declaration parses and names real rules")
def _():
    decls = {d.id: d for d in
             parse_family((RULES / "alpha-band.family").read_text())}
    assert set(decls) == {"fixture.alpha-band.exclusive",
                          "fixture.alpha-band.stable-add",
                          "fixture.reingestion.stable-add"}, sorted(decls)
    excl = decls["fixture.alpha-band.exclusive"]
    assert excl.rules == ("latest-high", "latest-low")
    assert "never both apply" in excl.says
    future = decls["fixture.alpha-band.stable-add"]
    assert future.collections == ("readings",)
    assert future.when == "taken-day > as-of-day"
    # the re-ingestion claim, which is what catches the second historical
    # defect: a tie-break on `fact-id !=` silenced the branch for two
    # identical results from two feeds
    dup = decls["fixture.reingestion.stable-add"]
    assert dup.when == "duplicate", dup.when
    assert dup.collections == ("readings",)
    validate(list(decls.values()),
             {p.stem for p in RULES.glob("*.rule")})


@check("the declaration is ungated, like the theorem already proved")
def _():
    # The plan's worked example writes `family fixture.alpha-band over
    # alpha`, and fixture has no `alpha` rule: `alpha` is a test-code
    # VALUE inside the rules. `Properties.lean:band_exclusive` proves
    # the claim for ALL readings, assuming only fact-id uniqueness — so the
    # claim is ungated, and a gate would have made `predicate` demand the
    # verdict of a rule nobody can decide.
    decls = parse_family((RULES / "alpha-band.family").read_text())
    assert all(d.gate is None for d in decls), [d.gate for d in decls]
    known = {p.stem for p in RULES.glob("*.rule")}
    assert "alpha" not in known
    gated = parse_family('family fixture.alpha-band over alpha\n'
                         '  exclusive: latest-high, latest-low\n')
    try:
        validate(gated, known)
    except FamilyError as exc:
        assert "is not a rule" in str(exc), str(exc)
    else:
        raise AssertionError("a gate naming a non-rule was accepted")


@check("a declaration naming a rule that does not exist is refused")
def _():
    # The companion to the gate check above, and it had no test: `validate`
    # could stop checking the rules a declaration is DECLARED OVER and
    # every suite stayed green. Nothing in a .family file can tell whether
    # a name is real, so this is the only place the mistake can be caught —
    # and without it `predicate` later asks for the verdict of a rule
    # nobody can decide, raises inside the search, and the run reports
    # "no counterexamples found".
    known = {p.stem for p in RULES.glob("*.rule")}
    for text, why in (
            ('family fixture.alpha-band\n'
             '  exclusive: latest-high, no-such-rule\n',
             "one name of two is unknown"),
            ('family fixture.alpha-band\n'
             '  exclusive: nope-one, nope-two\n',
             "both names are unknown"),
            ('family fixture.alpha-band\n'
             '  says "x"\n'
             '  stable-add: latest-high, alpha for readings when '
             'taken-day > as-of-day\n',
             "a test-code value read as a rule, the plan's own mistake")):
        decls = parse_family(text)
        try:
            validate(decls, known)
        except FamilyError as exc:
            assert "not among the rules" in str(exc), str(exc)
            # the message has to name the one that is wrong, not just fail
            assert ("no-such-rule" in str(exc) or "nope-one" in str(exc)
                    or "alpha" in str(exc)), str(exc)
        else:
            raise AssertionError(f"accepted a declaration where {why}")

    # and the valid case still passes, so the three refusals above are not
    # the function refusing everything
    validate(parse_family('family fixture.alpha-band\n'
                          '  exclusive: latest-high, latest-low\n'), known)


@check("every malformed .family file is refused, with its own error")
def _():
    files = sorted(MUST_FAIL.glob("*.family"))
    assert files, "the corpus is empty"
    for path in files:
        text = path.read_text()
        first = text.splitlines()[0]
        assert first.startswith("# expect:"), f"{path.name}: no header"
        want = first.split("expect:", 1)[1].strip()
        try:
            parse_family(text)
        except FamilyError as exc:
            assert want in str(exc), (
                f"{path.name}: refused for the wrong reason: {exc}")
        else:
            raise AssertionError(f"{path.name}: accepted")


@check("exclusive reads as at most one")
def _():
    decl = PropertyDecl(id="d.x", kind="exclusive", rules=("a", "b", "c"))
    holds = predicate(decl)
    assert holds({"a": 0, "b": 0, "c": 0})
    assert holds({"a": 1, "b": 0, "c": 0})
    assert not holds({"a": 1, "b": 1, "c": 0})
    assert not holds({"a": 1, "b": 1, "c": 1})


@check("a gate makes the claim vacuous when it does not hold")
def _():
    decl = PropertyDecl(id="d.x", kind="exclusive", rules=("a", "b"),
                        gate="g")
    holds = predicate(decl)
    assert not holds({"g": 1, "a": 1, "b": 1}), "in force: violated"
    assert holds({"g": 0, "a": 1, "b": 1}), "not in force: vacuous"


@check("implies takes the first rule as the antecedent")
def _():
    holds = predicate(PropertyDecl(id="d.x", kind="implies",
                                   rules=("a", "b", "c")))
    assert holds({"a": 0, "b": 0, "c": 0}), "false antecedent"
    assert holds({"a": 1, "b": 1, "c": 1})
    assert not holds({"a": 1, "b": 1, "c": 0})
    assert not holds({"a": 1, "b": 0, "c": 1})


@check("covers reads as at least one")
def _():
    holds = predicate(PropertyDecl(id="d.x", kind="covers", rules=("a", "b")))
    assert holds({"a": 1, "b": 0})
    assert not holds({"a": 0, "b": 0})


@check("a stable-* reading compares before with after")
def _():
    holds = predicate(PropertyDecl(
        id="d.x", kind="stable-add", rules=("a", "b"),
        collections=("readings",), when="taken-day > as-of-day"))
    before = {"a": 1, "b": 0}
    assert holds(before, dict(before)), "unchanged"
    assert not holds(before, {"a": 0, "b": 0}), "the change flipped a"
    assert not holds(before, {"a": 1, "b": 1}), "the change flipped b"


@check("a gate makes every kind vacuous, not just exclusive")
def _():
    # The gate was only checked on `exclusive`. A gate wired wrongly on one
    # of the other kinds reads as a violation on a snapshot the claim says
    # nothing about, and the search spends a kernel confirmation proving a
    # counterexample to a claim nobody made.
    cases = (
        ("covers", ("a", "b"), {"a": 0, "b": 0}, None),
        ("implies", ("a", "b"), {"a": 1, "b": 0}, None),
        ("stable-add", ("a", "b"), {"a": 1, "b": 0}, {"a": 0, "b": 0}),
        ("stable-retract", ("a", "b"), {"a": 1, "b": 0}, {"a": 0, "b": 0}),
    )
    for kind, rules, verdicts, after in cases:
        # `collections` and `when` belong to a change property only;
        # PropertyDecl refuses them on the others.
        change = {"collections": ("readings",),
                  "when": "taken-day > as-of-day"} if after else {}
        decl = PropertyDecl(id=f"d.{kind}", kind=kind, rules=rules, gate="g",
                            **change)
        holds = predicate(decl)
        in_force = dict(verdicts, g=1)
        off = dict(verdicts, g=0)
        after_on = dict(after, g=1) if after is not None else None
        after_off = dict(after, g=0) if after is not None else None
        assert not holds(in_force, after_on), (
            f"{kind}: the gate holds, so the claim is violated here")
        assert holds(off, after_off), (
            f"{kind}: the gate does not hold, so the claim is vacuous")


@check("every operator a `when` filter may use reads correctly")
def _():
    # The `when` filter decides whether a change is the kind the declaration
    # is about. It was once ignored altogether, and a retraction was offered
    # as evidence for a `stable-add` — a correct rule reported as broken. Of
    # the seven operators only `>` was exercised, because that is what the
    # shipped family happens to use.
    row = {"taken-day": 12}
    for when, expect in (
            ("taken-day > as-of-day", False),
            ("taken-day >= as-of-day", False),
            ("taken-day < as-of-day", True),
            ("taken-day <= as-of-day", True),
            ("taken-day = as-of-day", False),
            ("taken-day != as-of-day", True),
            ("taken-day > as-of-day - 3", True),
            ("taken-day < as-of-day - 3", False),
            ("taken-day = 12", True),
            ("taken-day != 12", False)):
        got = matches_when(row, when, as_of_day=14)
        assert got is expect, f"`when {when}` on day 14 read {got}"
    # a boundary, where >= and > must differ
    assert matches_when({"taken-day": 14}, "taken-day >= as-of-day",
                        as_of_day=14)
    assert not matches_when({"taken-day": 14},
                            "taken-day > as-of-day", as_of_day=14)
    # a string value, quoted in the filter
    assert matches_when({"source": "feed"}, 'source = "feed"', as_of_day=0)
    assert not matches_when({"source": "fax"}, 'source = "feed"', as_of_day=0)


@check("the `when` filter's other answers: absent, duplicate, unreadable")
def _():
    row = {"taken-day": 12}
    # No clause: the declaration is about every row it could be about.
    assert matches_when(row, None, as_of_day=14)
    assert matches_when(row, "", as_of_day=14)
    # `duplicate` is about the row's relation to the others, which this
    # function cannot see, so it defers to the caller rather than guessing.
    assert matches_when(row, DUPLICATE, as_of_day=14)
    assert matches_when(row, f"  {DUPLICATE}  ", as_of_day=14)
    # A row the filter asks about an attribute it does not carry is not a
    # row the declaration is about. Reading it as True would make every
    # declaration about every row.
    assert not matches_when({"source": "feed"},
                            "taken-day > as-of-day", as_of_day=14)
    assert not matches_when({"taken-day": None},
                            "taken-day > as-of-day", as_of_day=14)
    # Too few words to be a comparison at all.
    for bad in ("taken-day", "taken-day >"):
        try:
            matches_when(row, bad, as_of_day=14)
        except ValueError as exc:
            assert "when" in str(exc), exc
        else:
            raise AssertionError(f"`when {bad}` was accepted")


@check("a world set reports its size and its widest collection")
def _():
    ws = WorldSet(data={"readings": [{"fact-id": "a"}, {"fact-id": "b"}],
                        "dxs": [{"fact-id": "c"}]},
                  subject="pt-1", as_of_day=10)
    assert ws.size() == 3, ws.size()
    assert ws.widest() == 2, ws.widest()
    assert WorldSet(data={}, subject="pt-1", as_of_day=10).widest() == 0


@check("an operator a `when` filter cannot read is refused, not guessed")
def _():
    try:
        matches_when({"taken-day": 1}, "taken-day ~ as-of-day",
                     as_of_day=0)
    except ValueError as exc:
        assert "operator" in str(exc), exc
    else:
        raise AssertionError("an unreadable operator was accepted")


@check("a reading refuses a missing verdict instead of inventing one")
def _():
    # Returning False would be reported as a counterexample and spend a
    # kernel confirmation on nothing.
    holds = predicate(PropertyDecl(id="d.x", kind="exclusive",
                                   rules=("a", "b")))
    try:
        holds({"a": 1})
    except KeyError as exc:
        assert "no verdict for b" in str(exc), str(exc)
    else:
        raise AssertionError("a missing verdict was read as a value")
    change = predicate(PropertyDecl(id="d.y", kind="stable-add",
                                    rules=("a",), collections=("readings",)))
    try:
        change({"a": 1})
    except ValueError as exc:
        assert "needs the verdicts after" in str(exc), str(exc)
    else:
        raise AssertionError("a stable-* reading ran without the change")


if __name__ == "__main__":
    for name in PASS:
        print(f"  pass  {name}")
    for name, why in FAIL:
        print(f"  FAIL  {name}\n          {why}")
    print(f"\n{len(PASS)}/{len(PASS) + len(FAIL)} passed")
    sys.exit(1 if FAIL else 0)
