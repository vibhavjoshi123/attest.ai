"""Regression tests for the extensible core. No server and no Lean needed.

One test per property that was got wrong at least once. Each names the failure
it prevents rather than the function it calls.

    python3 tests/test_core.py
"""

from __future__ import annotations

import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from attest import (                                              # noqa: E402
    Certificate,
    Ingest,
    Recheck,
    Snapshot,
    Store,
    StoreConfig,
    UnknownSubject,
    VerificationError,
    as_of,
    dt,
    ident,
    make_snapshot,
    record,
    rulec,
    verdicts,
)
from attest.kernel import Check, Kernel, case_source                # noqa: E402

PASS, FAIL = [], []

SAMPLE_RULE = """
rule demo.pair v0.1
says "two different things"
subject holder
collection holdings : holding for subject via holder
conclude Bad when
  some holding a in holdings
  some holding b in holdings
  require a.item != b.item
"""


#: A schema in the form TypeDB's own `type_schema()` returns, so the type
#: bridge is exercised on the shape it actually gets.
SAMPLE_SCHEMA = """define
attribute fact-id,
    value string;
attribute source,
    value string;
attribute recorded-at,
    value datetime;
attribute test-code,
    value string @values("a", "b");
attribute reading,
    value integer;
attribute taken,
    value integer;
attribute note,
    value string;
attribute holder-id,
    value string;
entity holder,
    owns holder-id @key;
relation measurement,
    relates of @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1),
    owns test-code @card(1..1),
    owns reading @card(1..1),
    owns taken @card(1..1),
    owns note;
"""

THRESHOLD_RULE = """
rule demo.threshold v0.1
says "a reading at or above the limit"
subject holder
collection readings : measurement for subject via of
conclude OverLimit when
  some measurement m in readings
  require m.test-code = a
  require m.reading >= 70
"""

#: the same rule about the LATEST reading: the absence of a newer one
LATEST_RULE = """
rule demo.latest v0.1
says "the most recent reading is at or above the limit"
subject holder
collection readings : measurement for subject via of
conclude OverLimit when
  some measurement m in readings
  require m.reading >= 70
  none of
    some measurement n in readings
    require n.reading > m.reading
"""

#: and about a reading inside a window, which needs the instant being decided
WINDOW_RULE = """
rule demo.window v0.1
says "a recent reading is at or above the limit"
subject holder
collection readings : measurement for subject via of
conclude OverLimit when
  some measurement m in readings
  require m.reading >= 70
  require m.taken >= as-of-day - 180
"""


def check(name):
    def wrap(fn):
        try:
            fn()
            PASS.append(name)
        except Exception as exc:                                   # noqa: BLE001
            FAIL.append((name, f"{type(exc).__name__}: {exc}"))
        return fn
    return wrap


class FakeStore:
    """Records what would have been written; answers canned reads."""

    def __init__(self, rows=None):
        self.written, self._rows = [], rows or []
        self.queried: list[str] = []
        self.must_affect = False

    def write(self, queries, kind=None, *, must_affect=False):
        self.must_affect = must_affect
        self.written.extend(
            [queries] if isinstance(queries, str) else list(queries))

    def rows(self, query, tx=None):
        self.queried.append(query)
        return self._rows


def a_certificate(verdict="SAFE", scope=(), relied=()) -> Certificate:
    snapshot = make_snapshot("h-01", "2026-10-10T00:00:00", {"x": 1},
                             fact_ids=relied, scope=scope)
    return Certificate(
        verdict=verdict, rule="r v0.1", snapshot=snapshot, witnesses=[],
        witness_accepted=False, rule_shape="shape-sha", decided_by="negation",
        differential="agree", relied_on=list(relied),
        kernel_version="lean 4.35.0", library_sha256={}, schema_sha256="x",
        accepted=[], rejected=[{"reason": "none"}], proof=None, sha256="c0")


# ── 1. provenance and identifiers ───────────────────────────────────
@check("an unsafe identifier never reaches a query")
def _():
    for bad in ('x"; delete $all;', "a b", "", "x" * 200, "drop`"):
        try:
            ident(bad)
        except ValueError:
            continue
        raise AssertionError(f"accepted unsafe identifier {bad!r}")
    assert ident("item-a") == "item-a"
    assert ident("p.01:x@y+z") == "p.01:x@y+z"


@check("a malformed datetime never reaches a query")
def _():
    for bad in ("2026-13-01T00:00:00x", "yesterday", "2026-10-01", ""):
        try:
            dt(bad)
        except ValueError:
            continue
        raise AssertionError(f"accepted malformed datetime {bad!r}")
    assert dt("2026-10-01T00:00:00") == "2026-10-01T00:00:00"
    # sub-second precision is KEPT, not truncated: ledger times have to be
    # strictly increasing, and seconds are too coarse to guarantee that
    assert dt("2026-10-01T00:00:00.123456+00:00") == "2026-10-01T00:00:00.123456"


@check("as_of tests both halves: recorded by T and not retracted by T")
def _():
    fragment = as_of("$rx", "2026-10-10T00:00:00")
    assert "has recorded-at" in fragment
    assert "<= 2026-10-10T00:00:00" in fragment
    assert "not {" in fragment and "retracted-at" in fragment, (
        "a fragment without the retraction half keeps deciding cases from "
        "facts that have been corrected")


# ── 2. the ledger only moves forward ────────────────────────────────
@check("a ledger time is strictly later than the mark, not merely not-earlier")
def _():
    """Two writes inside one second both compared equal and both passed.

    A decision "as of" that second taken between the two commits sees the
    first fact and not the second; the second then lands inside an
    already-decided snapshot and replay breaks. Measured on a live server: a
    compare-and-set of X against X matches and commits.
    """
    store = FakeStore(rows=[{"h": "2026-10-05T00:00:00"}])
    same = Ingest(store, clock=lambda: "2026-10-05T00:00:00").now()
    assert same > "2026-10-05T00:00:00", (
        f"a second write in the same second produced {same!r}, which is not "
        f"strictly later than the mark")
    assert Ingest._after("2026-10-05T00:00:00.000001") == \
        "2026-10-05T00:00:00.000002"


@check("an older database without a ledger is seeded from its facts")
def _():
    """Otherwise the first write after an upgrade has no mark to check
    against, and can be backdated under every fact already stored."""
    class Store2(FakeStore):
        def rows(self, query, tx=None):
            self.queried.append(query)
            if "isa ledger" in query:
                return []                      # no ledger row yet
            return [{"m": "2026-11-01T00:00:00"}]

    store = Store2()
    ingest = Ingest(store)
    assert ingest.high_water() == "2026-11-01T00:00:00", (
        "fell back to no mark, so the first write could be backdated")
    try:
        Ingest(store, clock=lambda: "2026-01-01T00:00:00").now()
    except ValueError as exc:
        assert "backdating refused" in str(exc)
        return
    raise AssertionError("accepted a fact before every fact already stored")


@check("an isolation conflict at commit reads like a lost compare-and-set")
def _():
    """Overlapping writers BOTH match their compare-and-set — each sees the
    old value in its own snapshot. The engine stops the second at commit,
    with a raw driver error. If that does not surface as the same failure,
    retry logic misses it entirely."""
    import inspect
    from attest import store as store_mod
    src = inspect.getsource(store_mod.Store.write)
    assert "STC2" in src and "ConcurrentWrite" in src, (
        "a commit-time isolation conflict is the same failure as a lost CAS "
        "and must read the same way")


@check("a lost race stays a ConcurrentWrite; a missing record is not called one")
def _():
    """Found against a live store. `Ingest.record` re-raised every failure
    as a plain "the ledger moved" error, so (a) a ConcurrentWrite lost its
    type and retry logic could not catch it, and (b) a fact naming a record
    that does not exist was reported as a concurrent writer.

    The fake raises exactly what `Store.write` raises — `WriteMatchedNothing`
    carrying the index of the query that missed — rather than reproducing its
    message. An earlier version matched on text, which quietly coupled
    `advance[:60]` here to `query[:90]` there: shortening either would have
    turned a lost compare-and-set into "your data is missing"."""
    from attest.store import ConcurrentWrite, WriteMatchedNothing

    class Raising(FakeStore):
        def __init__(self, fail):
            super().__init__(rows=[{"h": "2026-10-05T00:00:00"}])
            self.fail = fail            # "commit", or index of the query that misses

        def write(self, queries, kind=None, *, must_affect=False):
            if self.fail == "commit":
                raise ConcurrentWrite("STC2")
            raise WriteMatchedNothing(self.fail, queries[self.fail])

    def record(store):
        Ingest(store, clock=lambda: "2026-10-09T00:00:00").record(
            'match $d isa item, has name "no-such-item"; insert $x isa thing;')

    # overlapping writer, stopped at commit
    try:
        record(Raising("commit"))
    except ConcurrentWrite:
        pass
    else:
        raise AssertionError("a commit-time conflict lost its ConcurrentWrite type")

    # sequential writer: the ledger compare-and-set (query 0) matched nothing
    try:
        record(Raising(0))
    except ConcurrentWrite:
        pass
    else:
        raise AssertionError("a lost compare-and-set was not a ConcurrentWrite")

    # the caller's own match (query 1) found nothing
    try:
        record(Raising(1))
    except ConcurrentWrite:
        raise AssertionError("a missing record was reported as a concurrent writer")
    except VerificationError as exc:
        assert "no-such-item" in str(exc), exc
    else:
        raise AssertionError("a write that matched nothing reported success")


@check("a certificate hashes the same however the search ordered its witnesses")
def _():
    """Found by running the same decision twice and diffing the traces: two
    runs over the same facts wrote different traces, because TypeDB
    functions have bag semantics and no guaranteed order.

    `witnesses` is hashed into `certificate_sha256`, so the certificate for
    one decision had no stable identity — and a stable identity is most of
    what a certificate is for. `decide` already sorted when CHOOSING a
    witness; the recorded form has to be canonical too."""
    base = a_certificate().__dict__
    one = Certificate(**{**base,
                         "witnesses": [["rx-1", "in-1"], ["rx-2", "in-2"]]})
    two = Certificate(**{**base,
                         "witnesses": [["rx-2", "in-2"], ["rx-1", "in-1"]]})
    # canonical on construction, whichever order the search returned
    assert one.witnesses == two.witnesses == [["rx-1", "in-1"],
                                              ["rx-2", "in-2"]]
    assert (one.as_dict()["certificate_sha256"]
            == two.as_dict()["certificate_sha256"]), (
        "the same decision hashed differently depending on the order the "
        "search happened to return its witnesses in")


@check("the high-water mark is one row, not a scan of every fact")
def _():
    store = FakeStore(rows=[{"h": "2026-10-05T00:00:00"}])
    Ingest(store, clock=lambda: "2026-12-01T00:00:00").high_water()
    assert store.queried, "high_water issued no query"
    assert all("isa ledger" in q for q in store.queried), (
        "reading the mark by scanning facts is O(all facts) on every single "
        f"write, for one scalar: {store.queried}")


@check("a fact write advances the ledger by compare-and-set")
def _():
    """Two writers must not both pass the clock check.

    The ledger move matches on the value this call read, so a writer that
    advanced it in between makes the match find nothing — and `must_affect`
    turns that into a rollback of the whole transaction.
    """
    store = FakeStore(rows=[{"h": "2026-10-05T00:00:00"}])
    ingest = Ingest(store, clock=lambda: "2026-10-09T00:00:00")
    ingest.record("insert $x isa thing;")
    joined = " ".join(store.written)
    assert "isa ledger" in joined and "$h == 2026-10-05T00:00:00" in joined, (
        f"the ledger advance is not a compare-and-set: {store.written}")
    assert "update $l has high-water 2026-10-09T00:00:00" in joined
    assert store.must_affect, (
        "without must_affect a lost compare-and-set writes the fact anyway")
    assert "insert $x isa thing;" in store.written, (
        "the fact and the ledger move must be in the same transaction")


class LedgerStore(FakeStore):
    """Answers the ledger row and the fact-max reduce separately.

    `Ingest.now` asks two different questions now — "where is the mark?"
    and "when was the last real fact?" — because a sealed as-of window
    moves the first without moving the second.
    """

    def __init__(self, mark=None, last_fact=None):
        super().__init__()
        self.mark, self.last = mark, last_fact

    def rows(self, query, tx=None):
        self.queried.append(query)
        if "reduce" in query:
            return [{"m": self.last}] if self.last else []
        return [{"h": self.mark}] if self.mark else []


@check("backdating a fact is refused")
def _():
    # Judged against the last recorded FACT, not against the mark, which a
    # sealed as-of window also moves.
    store = LedgerStore(mark="2026-10-05T00:00:00",
                        last_fact="2026-10-05T00:00:00")
    ingest = Ingest(store, clock=lambda: "2026-09-01T00:00:00")
    try:
        ingest.now()
    except ValueError as exc:
        assert "backdating refused" in str(exc)
        return
    raise AssertionError("accepted a fact before the last recorded fact")


@check("a fact at or after the high-water mark is accepted")
def _():
    store = FakeStore(rows=[{"h": "2026-10-05T00:00:00"}])
    assert Ingest(store, clock=lambda: "2026-10-05T00:00:00").now()
    assert Ingest(store, clock=lambda: "2026-12-01T00:00:00").now()


@check("retraction is an append, and never a second one")
def _():
    store = FakeStore(rows=[])
    Ingest(store, clock=lambda: "2026-10-05T00:00:00").retract("f-2")
    joined = " ".join(store.written)
    assert "insert $f has retracted-at" in joined
    assert "not { $f has retracted-at" in joined, (
        "without the guard a second retraction would add a second timestamp")
    assert "delete" not in joined
    assert "isa ledger" in joined, (
        "a retraction is a ledger event too, or the clock check misses it")


# ── 3. the kernel ───────────────────────────────────────────────────
@check("the case source is deterministic")
def _():
    args = ("Case_x", ["M"], ["M"], "def s := 1\n", "holds", "P s", "by decide")
    assert case_source(*args) == case_source(*args)
    assert "#print axioms Case_x.holds" in case_source(*args), (
        "without the axiom print nothing constrains what the proof used")


@check("a kernel that does not finish has not accepted anything")
def _():
    kernel = Kernel(pathlib.Path("/nonexistent"), case_dir=pathlib.Path("/tmp"))
    kernel._built = True                       # isolate the check from the build

    def boom(*_a, **_k):
        raise subprocess.TimeoutExpired(cmd="lake", timeout=1)

    original, subprocess.run = subprocess.run, boom
    try:
        result = kernel.check("Case_x", [], [], "", "holds", "P", "by decide")
    finally:
        subprocess.run = original
    assert result.accepted is False
    assert "did not complete" in (result.reason or "")


@check("a package that does not build has accepted nothing")
def _():
    kernel = Kernel(pathlib.Path("/nonexistent"), case_dir=pathlib.Path("/tmp"))

    def boom(*_a, **_k):
        raise subprocess.TimeoutExpired(cmd="lake", timeout=1)

    original, subprocess.run = subprocess.run, boom
    try:
        result = kernel.check("Case_x", [], [], "", "holds", "P", "by decide")
    finally:
        subprocess.run = original
    assert result.accepted is False, (
        "without a build the kernel loads whatever oleans happen to be there, "
        "so the drift check certifies source the kernel never ran")
    assert "build" in (result.reason or "").lower()


@check("an axiom outside the allowed set is a rejection")
def _():
    kernel = Kernel(pathlib.Path("/tmp"))
    assert "propext" in kernel.allowed_axioms
    assert "sorryAx" not in kernel.allowed_axioms
    kernel.allow("att_reviewer_signed")
    assert "att_reviewer_signed" in kernel.allowed_axioms, (
        "a signed attestation has to be nameable, or it cannot be audited")


# ── 4. the rule, and what the core will and will not record ─────────
@check("a verdict names what was proved, not a word nobody proved")
def _():
    holds, fails = verdicts({"conclusion": "Bad"})
    assert (holds, fails) == ("Bad", "not Bad"), (
        "giving the negation a name of its own — the word the domain happens "
        "to use for the reassuring case — would put a claim in the "
        "certificate that no theorem established")


@check("one rule source compiles to a Lean rule and a TypeQL search")
def _():
    rule = rulec.parse(SAMPLE_RULE)
    assert rule["id"] == "demo.pair"
    assert rule["conclusion"] == "Bad"
    assert [s["kind"] for s in rule["steps"]].count("some") == 2
    first, second = rulec.fn_names(rule)
    assert rule["sha"][:12] in first, (
        "the function name carries the rule hash, so a deployed search that "
        "is not this rule cannot be mistaken for one that is")
    assert first != second


@check("an ERROR verdict is refused, not stored")
def _():
    store = FakeStore()
    try:
        record(store, a_certificate("ERROR"), "holder", "ref",
               "2026-10-10T00:00:00")
    except VerificationError:
        assert store.written == [], "a refused decision still wrote something"
        return
    raise AssertionError("recorded a verdict the kernel never settled")


@check("a decision, its reliance and its coverage go in one write")
def _():
    store = FakeStore()
    certificate = a_certificate(
        "SAFE", scope=[("thing", "name", "item-a")], relied=["f-1"])
    record(store, certificate, "holder", "ref", "2026-10-10T00:00:00")
    joined = " ".join(store.written)
    assert "isa decision" in joined
    assert "insert reliance" in joined
    assert "insert coverage" in joined, (
        "without coverage edges, a decision is invisible to the ADDITION half "
        "of impact analysis")
    assert '$x isa thing, has name "item-a"' in joined, (
        "binding a covered item by attribute alone is ambiguous when another "
        "type owns the same attribute")
    assert store.must_affect, (
        "without must_affect a reliance edge whose fact does not exist is "
        "silently skipped, and the decision looks unaffected forever after")


# ── 5. snapshots ────────────────────────────────────────────────────
@check("a snapshot with a fact-id twice is refused")
def _():
    """The store guarantees `fact-id @key`; the Lean type cannot. The
    exclusivity proofs for a rule family assume a fact-id identifies one
    record, and a kernel audit confirmed the assumption is load-bearing:
    supply a snapshot Lean permits with one id on two rows and both branches
    of a binary gate hold, each with a valid proof. The invariant is
    enforced here, the one place that sees every row at once."""
    rows = [{"fact-id": "f-1", "v": 1}, {"fact-id": "f-1", "v": 2}]
    try:
        make_snapshot("h-1", "2026-10-10T00:00:00", {"labs": rows})
    except VerificationError as exc:
        assert "appears twice" in str(exc), exc
    else:
        raise AssertionError("a duplicate fact-id was accepted")
    # across two collections too, not just within one
    try:
        make_snapshot("h-1", "2026-10-10T00:00:00",
                      {"a": [{"fact-id": "f-1"}], "b": [{"fact-id": "f-1"}]})
    except VerificationError:
        pass
    else:
        raise AssertionError("a duplicate across collections was accepted")


@check("the snapshot hash covers the facts, not the ordering of a dict")
def _():
    one = make_snapshot("p", "2026-10-10T00:00:00", {"a": 1, "b": 2})
    two = make_snapshot("p", "2026-10-10T00:00:00", {"b": 2, "a": 1})
    assert one.sha256 == two.sha256
    three = make_snapshot("p", "2026-10-10T00:00:00", {"a": 1, "b": 3})
    assert one.sha256 != three.sha256


@check("a snapshot carries what it looked at, not just what it used")
def _():
    snapshot = make_snapshot(
        "p", "2026-10-10T00:00:00", {}, fact_ids=["f-1"],
        scope=[("thing", "name", "item-a"),
               ("thing", "name", "item-b")])
    assert snapshot.fact_ids == ("f-1",)
    assert len(snapshot.scope) == 2


# ── 6. empty is not an answer ───────────────────────────────────────
@check("a write that matched nothing aborts instead of reporting success")
def _():
    class Rows:
        @staticmethod
        def is_concept_rows():
            return True

        @staticmethod
        def as_concept_rows():
            return iter(())

    class Tx:
        def __init__(self):
            self.rolled_back = self.committed = False

        def query(self, _q):
            return type("P", (), {"resolve": staticmethod(lambda: Rows())})()

        def rollback(self):
            self.rolled_back = True

        def commit(self):
            self.committed = True

        def __enter__(self):
            return self

        def __exit__(self, *_):
            return False

    tx = Tx()
    store = Store.__new__(Store)
    store.database = "db"
    store.driver = type("D", (), {"transaction": lambda *_a, **_k: tx})()
    try:
        store.write(["match $x isa nothing; insert $y isa thing;"],
                    kind="WRITE", must_affect=True)
    except VerificationError as exc:
        assert "matched nothing" in str(exc)
        assert tx.rolled_back and not tx.committed, (
            "a write that matched nothing must roll the transaction back, or "
            "a decision is stored with its edges silently missing")
        return
    raise AssertionError("a match-insert that matched nothing reported success")


@check("an unknown subject is refused, not decided as an empty case")
def _():
    class EmptyTx:
        @staticmethod
        def query(_q):
            return type("P", (), {"resolve": staticmethod(
                lambda: type("A", (), {
                    "as_concept_rows": staticmethod(lambda: iter(()))})())})()

    store = Store.__new__(Store)
    store.database = "db"
    try:
        Store.require(store, EmptyTx(), '$x isa holder;', "no h-99")
    except UnknownSubject as exc:
        assert "unknown subject" in str(exc)
        return
    raise AssertionError(
        "an absent subject exported nothing, and nothing is vacuously safe")


@check("impact analysis refuses to run half of itself silently")
def _():
    from attest import affected_decisions
    try:
        affected_decisions(FakeStore(), "f-2")
    except TypeError as exc:
        assert "scope_anchors" in str(exc)
        return
    raise AssertionError(
        "omitting anchors returned only retractions, so a fact added later "
        "would leave every earlier decision looking valid")


@check("no core role is left at the @card(0..1) default")
def _():
    """`relates` defaults to 0..1, exactly like `owns`.

    Left at the default, a reliance edge with a decision and no evidence is
    schema-legal — a dangling link the impact queries can never see. Verified
    against a live 3.8.0 server before this test was written.
    """
    import re
    text = (pathlib.Path(__file__).resolve().parents[1]
            / "attest" / "core.tql").read_text()
    body = text[text.index("relation decision"):]
    bare = [m.group(0) for m in re.finditer(r"relates \w+(?! @card)[,;]", body)]
    assert not bare, f"roles left at the 0..1 default: {bare}"


@check("a decision's own subject can be covered")
def _():
    text = (pathlib.Path(__file__).resolve().parents[1]
            / "attest" / "core.tql").read_text()
    block = text[text.index("entity subject"):]
    block = block[:block.index(";")]
    assert "plays coverage:item" in block, (
        "a fact recorded later is usually about the subject; without this "
        "the addition half of impact analysis reaches the decision only "
        "indirectly, through whatever else the export touched")


@check("prose cannot escape the Lean comment it is written into")
def _():
    """`says` is interpolated into /- … -/ and /-- … -/ in the generated rule.

    A value containing `-/` and a newline closes the comment and the rest
    elaborates as Lean — demonstrated reaching `initialize`, i.e. code
    execution at build time, from a field a domain expert writes as a
    sentence. The drift check cannot help: the generated file genuinely is
    what the rule compiles to.
    """
    hostile = SAMPLE_RULE.replace(
        'says "two different things"',
        'says "ok -/\\ninitialize pwn : Unit <- pure ()\\n/-- x"')
    try:
        rulec.parse(hostile)
    except rulec.RuleError as exc:
        assert "comment" in str(exc) or "single line" in str(exc)
        return
    raise AssertionError("prose escaped into the generated Lean module")


@check("a rule body that proves nothing is refused")
def _():
    empty = """
rule demo.vacuous v0.1
says "nothing at all"
subject holder
collection holdings : holding for subject via holder
conclude Eligible when
"""
    try:
        rulec.parse(empty)
    except rulec.RuleError as exc:
        assert "at least one" in str(exc)
        return
    raise AssertionError(
        "an empty body compiles to Prop := True — on an Eligible-style "
        "conclusion that approves everyone, with a real kernel proof")


@check("a conclusion that is not a Lean identifier is refused")
def _():
    bad = SAMPLE_RULE.replace("conclude Bad when", "conclude Bad snap; axiom x when")
    try:
        rulec.parse(bad)
    except (rulec.RuleError, AssertionError):
        return
    raise AssertionError("the conclusion is interpolated into a statement")


@check("a contradicted verdict is not recorded")
def _():
    store = FakeStore()
    certificate = a_certificate("Bad", relied=["f-1"])
    certificate.differential = (
        "DISAGREE: the search found nothing; the kernel proved Bad")
    try:
        record(store, certificate, "holder", "ref", "2026-10-10T00:00:00")
    except VerificationError as exc:
        assert "contradicted" in str(exc)
        assert store.written == []
        return
    raise AssertionError(
        "a verdict the search contradicts was stored, with the only trace "
        "of the contradiction in a prose field")


@check("a witness built from facts outside the snapshot yields no verdict")
def _():
    """The search found a conflict the export did not produce.

    That is a fact about the EXPORT. Proceeding would prove the negation over
    a snapshot already known to be incomplete and record it — "missing data
    means safe" through a side door.
    """
    import inspect
    from attest import runner
    src = inspect.getsource(runner.decide)
    head = src[src.index("if term is None:"):]
    body = head[:head.index("else:")]
    assert "_unsettled" in body or "ERROR" in body, (
        "an unusable witness must terminate, not fall through to proving "
        "the negation over the incomplete snapshot")
    assert "return" in body, "control continued past the incomplete snapshot"


@check("a decision as of a future date is refused")
def _():
    import inspect
    from attest import runner
    src = inspect.getsource(runner.decide)
    assert "in the future" in src, (
        "a fact written after a future as-of date falls inside the window "
        "and changes the snapshot, so the certificate stops replaying")


@check("a rule binding the same variable twice is refused")
def _():
    twice = SAMPLE_RULE.replace(
        "some holding b in holdings", "some holding a in holdings")
    try:
        rulec.parse(twice)
    except rulec.RuleError as exc:
        assert "twice" in str(exc)
        return
    raise AssertionError(
        "Lean shadows the first binder and TypeQL reuses it, so one source "
        "compiles to two different rules")


@check("a case file carrying a forbidden construct is refused")
def _():
    """`debug.skipKernelTC` is an ordinary option that leaves no trace.

    ModuleData has no options field, so a compiled module records nothing
    about whether it was kernel-checked, and #print axioms cannot reveal it.
    The only defence at this layer is refusing the construct outright.
    """
    from attest.kernel import forbidden
    for bad in ("set_option debug.skipKernelTC true",
                "axiom cheat : False",
                "initialize x : Unit <- pure ()",
                "#eval 1",
                "unsafe def f := 0",
                "example := native_decide"):
        assert forbidden(bad) is not None, f"accepted {bad!r}"


@check("snapshot data cannot trip the construct check")
def _():
    """The snapshot is data and may contain anything a source recorded."""
    from attest.kernel import forbidden
    benign = ('def snap : Snapshot := { note := "set_option and axiom and '
              'initialize appear in this chart note" }')
    assert forbidden(benign) is None, (
        "string literals must be blanked before the scan, or real data is "
        "refused as an attack")


@check("a compiled rule sets only elaboration budgets, nothing dangerous")
def _():
    """`kernel.forbidden` scans case files and stored proofs, not generated
    rule modules — so if the compiler may write `set_option` at all, the set
    it may write has to be closed. `debug.skipKernelTC` in a rule module
    would make proofs that were never kernel-checked look checked, and the
    denylist would never see it."""
    import re
    from attest import typebridge as tb
    model = tb.parse(SAMPLE_SCHEMA)
    for src in (THRESHOLD_RULE, LATEST_RULE, WINDOW_RULE):
        lean = rulec.compile_lean(rulec.parse(src), model, "X.R", "X.S")
        for line in re.findall(r"^set_option .*$", lean, re.M):
            assert line in rulec.SAFE_OPTIONS, (
                f"compiled rule sets an option outside the allowlist: {line!r}")
    # and the allowlist itself contains nothing that affects the kernel
    for opt in rulec.SAFE_OPTIONS:
        assert re.match(
            r"^set_option (synthInstance\.\w+|maxRecDepth|maxHeartbeats) ",
            opt), f"{opt!r} is not purely an elaboration budget"


@check("a rule's shape tells a rename apart from a changed threshold")
def _():
    """The exact hash answers "is this the same text". It cannot answer "is
    this the same QUESTION", and that is what a stored decision needs when a
    rule is edited. Without it, renaming one variable orphans every stored
    decision and nothing distinguishes that from a changed threshold.

    Why3 makes exactly this distinction — an exact hash for identity, a
    shape for near identity — and it is the thing that keeps a proof session
    useful across specification edits instead of discarding it."""
    base = rulec.parse(LATEST_RULE)

    cosmetic = {
        "renamed variable": LATEST_RULE.replace(" m in ", " zz in ")
                                       .replace("m.reading", "zz.reading")
                                       .replace("> m.", "> zz."),
        "renamed collection": LATEST_RULE.replace("readings", "samples"),
        "reworded says": LATEST_RULE.replace(
            "the most recent reading is at or above the limit", "anything"),
        "bumped version": LATEST_RULE.replace("v0.1", "v9.9"),
        "different id": LATEST_RULE.replace("demo.latest", "other.name"),
    }
    for label, text in cosmetic.items():
        other = rulec.parse(text)
        assert rulec.same_obligation(base, other), (
            f"{label} changed the obligation, but it is the same question")
        assert other["sha"] != base["sha"], (
            f"{label} should still change the exact hash")

    meaningful = {
        "threshold": LATEST_RULE.replace(">= 70", ">= 80"),
        "operator": LATEST_RULE.replace("m.reading >= 70", "m.reading > 70"),
        "negation dropped": LATEST_RULE.replace(
            "  none of\n    some measurement n in readings\n"
            "    require n.reading > m.reading\n", ""),
    }
    for label, text in meaningful.items():
        assert not rulec.same_obligation(base, rulec.parse(text)), (
            f"{label} is a different question and must not match")

    # and the shape is a stable hash, not an object identity
    assert rulec.shape_sha(base) == rulec.shape_sha(rulec.parse(LATEST_RULE))


@check("a family of rules over one schema compiles to one module each")
def _():
    """One rule per branch is the normal shape for anything with more than
    one outcome. Taking only the first id segment put the whole family in
    `Billing.lean`: the last written won, and the drift check then reported
    Drift on a rule nobody had touched."""
    one = rulec.parse(SAMPLE_RULE.replace("rule demo.pair",
                                          "rule billing.duplicate-claim"))
    two = rulec.parse(SAMPLE_RULE.replace("rule demo.pair",
                                          "rule billing.late-filing"))
    assert rulec.module(one, "L.Rules") == "L.Rules.Billing.DuplicateClaim"
    assert rulec.module(two, "L.Rules") == "L.Rules.Billing.LateFiling"
    assert (rulec.lean_path(one, "/d", "L.Rules")
            != rulec.lean_path(two, "/d", "L.Rules")), (
        "two rules of one family must not compile to the same file")
    assert rulec.lean_path(one, "/d", "L.Rules").endswith(
        "/d/L/Rules/Billing/DuplicateClaim.lean")
    # and the deployed searches are named apart too, not only hash-tagged
    first = rulec.fn_names(one)[0].split("_witness_")[0]
    second = rulec.fn_names(two)[0].split("_witness_")[0]
    assert first != second, (
        f"two searches named {first!r} differing only by hash are unreadable "
        f"in a schema dump")


@check("`is-a` with two closures declared is refused")
def _():
    two = SAMPLE_RULE.replace(
        "conclude Bad when",
        "closure up over holdings from a to b\n"
        "closure down over holdings from b to a\n"
        "conclude Bad when").replace(
        "require a.item != b.item",
        "require a.item is-a b.item")
    try:
        rulec.parse(two)
    except rulec.RuleError as exc:
        assert "closures" in str(exc) or "closure" in str(exc)
        return
    raise AssertionError(
        "both compilers resolve is-a to closures[0], so two closures are "
        "wrong identically and the differential cannot see it")


@check("an integer attribute reaches Lean as Int, not String")
def _():
    """Every attribute used to become `String`. A threshold rule over a
    string quantity cannot be compiled at all — Lean's String has no `≤` —
    so the rule language could express equality and nothing else."""
    from attest import typebridge as tb
    model = tb.parse(SAMPLE_SCHEMA)
    kinds = {name: (lean_type, how)
             for name, _f, lean_type, how in tb.fields(model, "measurement")}
    assert kinds["reading"] == ("Int", "int"), kinds["reading"]
    assert kinds["test-code"] == ("TestCode", "enum"), kinds["test-code"]
    assert kinds["note"] == ("Option String", "str?"), kinds["note"]


@check("a threshold compiles to the same bound in Lean and in TypeQL")
def _():
    """The two forms are the whole point: if the kernel's bound and the
    search's bound can differ, the differential is comparing two rules."""
    from attest import typebridge as tb
    model = tb.parse(SAMPLE_SCHEMA)
    rule = rulec.parse(THRESHOLD_RULE)
    lean = rulec.compile_lean(rule, model, "X.Rules", "X.Schema")
    tql = rulec.compile_typeql(rule, model)
    assert "m.reading ≥ 70" in lean, lean
    assert "$m_reading >= 70;" in tql, tql
    # and the number is not quoted into a string on either side
    assert '"70"' not in lean and '"70"' not in tql


@check("an ordering on a value that is not a number is refused")
def _():
    """TypeQL would compare strings lexicographically and answer; Lean has
    no `≤` on String, so the generated module would not build. The refusal
    has to come from the rule compiler, where it can name the rule line."""
    from attest import typebridge as tb
    model = tb.parse(SAMPLE_SCHEMA)
    for bad in ("require m.test-code >= a",
                "require m.reading >= seven",
                "require m.reading = a",
                "require m.note >= 3"):
        src = THRESHOLD_RULE.replace("require m.reading >= 70", bad)
        try:
            rulec.compile_lean(rulec.parse(src), model, "X.Rules", "X.Schema")
        except rulec.RuleError:
            continue
        raise AssertionError(f"not refused: {bad}")


@check("a Lean literal never carries the previous field's value")
def _():
    """`lean_literal` had no final `else`: an unhandled kind left `lit`
    holding the last field's literal and wrote it under this field's name —
    a value the store never held, inside a proof term the kernel accepts."""
    from attest import typebridge as tb
    model = tb.parse(SAMPLE_SCHEMA)
    row = {"of": "h-1", "fact-id": "m-1", "source": "s",
           "recorded-at": "2026-01-01T00:00:00", "test-code": "a",
           "reading": 78, "taken": 20744, "note": None}
    out = tb.lean_literal(model, "measurement", row)
    assert "reading := 78" in out, out
    assert "note := none" in out, out
    # a kind the writer does not know about must raise, not reuse
    try:
        tb.lean_literal.__globals__["fields"]
    except KeyError:                                           # pragma: no cover
        pass
    original = tb.fields
    tb.fields = lambda m, t: [("mystery", "mystery", "Nat", "nat")]
    try:
        tb.lean_literal(model, "measurement", {"mystery": 1})
    except ValueError as exc:
        assert "no Lean literal" in str(exc), exc
    else:
        raise AssertionError("an unknown field kind was silently accepted")
    finally:
        tb.fields = original


@check("`none of` compiles to a negation in both forms, not to nothing")
def _():
    """Absence is half of most real rules — "no newer reading", "nothing
    excludes this". If the search negates and the authority does not (or the
    reverse), the two disagree on every case where the absence matters."""
    from attest import typebridge as tb
    model = tb.parse(SAMPLE_SCHEMA)
    rule = rulec.parse(LATEST_RULE)
    lean = rulec.compile_lean(rule, model, "X.Rules", "X.Schema")
    tql = rulec.compile_typeql(rule, model)
    assert "¬ (∃ n ∈ s.readings," in lean, lean
    # the block's own `not {` is at the start of a line; the `not {` inside a
    # fact's retraction guard is not the one this test is about
    block = "\n  not {"
    assert block in tql and "$n_reading > $m_reading;" in tql, tql
    # the binder inside a negation names no witness fact: there is no fact
    assert tql.count("has fact-id") == 1, tql
    # and the outer variable's field is bound OUTSIDE the negation, or the
    # binding is local to it and the outer body never makes it
    assert tql.index("$m has reading") < tql.index(block), tql


@check("a binder inside `none of` is local to it")
def _():
    for bad, why in (
        (LATEST_RULE + "  require n.reading >= 1\n", "inner binder leaked"),
        (LATEST_RULE.replace("require n.reading > m.reading",
                             "require n.reading > q.reading"), "unbound"),
        (LATEST_RULE.replace("""  none of
    some measurement n in readings
    require n.reading > m.reading""",
                             """  none of
    require m.reading > 1"""), "no binder in the block"),
    ):
        try:
            rulec.parse(bad)
        except rulec.RuleError:
            continue
        raise AssertionError(f"not refused: {why}")


@check("`as-of-day` is one number, shared by the authority and the search")
def _():
    """A window like "within six months" is a statement about now. If the
    kernel and the search each worked out "now" for themselves they could
    land on different days, and the differential would be comparing two
    different questions."""
    from attest import typebridge as tb
    from attest.runner import as_of_day
    model = tb.parse(SAMPLE_SCHEMA)
    rule = rulec.parse(WINDOW_RULE)
    assert rulec.uses_as_of(rule)
    lean = rulec.compile_lean(rule, model, "X.Rules", "X.Schema")
    tql = rulec.compile_typeql(rule, model)
    assert "asOfDay : Int" in lean, "the Snapshot has to carry the instant"
    assert "m.taken ≥ (s.asOfDay - 180)" in lean, lean
    assert "$asof_day: integer" in tql, tql
    assert "let $d1 = $asof_day - 180;" in tql, tql
    # truncated to a whole day, so a re-run later the same day replays
    assert as_of_day("2026-10-18T09:30:00") == as_of_day("2026-10-18T23:59:59")
    assert as_of_day("1970-01-01T00:00:00") == 0
    # a rule that says nothing about time keeps the Snapshot it had
    plain = rulec.parse(THRESHOLD_RULE)
    assert not rulec.uses_as_of(plain)
    assert "asOfDay" not in rulec.compile_lean(plain, model, "X.R", "X.S")
    assert "$asof_day" not in rulec.compile_typeql(plain, model)


@check("`as-of-day` compared with a non-number is refused")
def _():
    from attest import typebridge as tb
    model = tb.parse(SAMPLE_SCHEMA)
    for bad in ("require m.test-code >= as-of-day",
                "require m.note = as-of-day"):
        src = WINDOW_RULE.replace("require m.taken >= as-of-day - 180", bad)
        try:
            rulec.compile_lean(rulec.parse(src), model, "X.Rules", "X.Schema")
        except rulec.RuleError:
            continue
        raise AssertionError(f"not refused: {bad}")


#: a schema with a reference hierarchy, for the closure tests
GROUPED_SCHEMA = """define
attribute fact-id,
    value string;
attribute source,
    value string;
attribute recorded-at,
    value datetime;
attribute code,
    value string;
attribute holder-id,
    value string;
entity holder,
    owns holder-id @key,
    plays marking:of;
entity tag,
    owns code @key,
    plays marking:tag,
    plays group-isa:child,
    plays group-isa:parent,
    plays kind-isa:narrow,
    plays kind-isa:broad;
relation kind-isa,
    relates narrow @card(1..1),
    relates broad @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1);
relation group-isa,
    relates child @card(1..1),
    relates parent @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1);
relation marking,
    relates of @card(1..1),
    relates tag @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1);
"""

NAMED_RULE = """
rule demo.named v0.1
says "marked with something under the watched group"
subject holder
collection marks  : marking for subject via of
collection groups : group-isa
closure under over groups from child to parent
conclude Watched when
  some marking m in marks
  require m.tag is-a watched
"""

#: a rule that walks TWO hierarchies, which is what more than one outcome or
#: more than one kind of reference data actually needs
TWO_CLOSURE_RULE = """
rule demo.two v0.1
says "a holder marked under the watched group by a tag that is also a kind of alpha"
subject holder
collection marks  : marking   for subject via of
collection groups : group-isa
collection kinds  : kind-isa
closure under over groups from child to parent
closure kind-of over kinds from narrow to broad
conclude Watched when
  some marking m in marks
  require m.tag under watched
  require m.tag kind-of alpha
"""


@check("a rule can name a particular entity, comparing the same key in both")
def _():
    """Naming an entity is a basic rule shape. In Lean a role IS the
    player's key, so the comparison is a string one; TypeQL binds the entity,
    so comparing it to a string fails at `define` or quietly means something
    else. TypeQL is made to compare the key instead."""
    from attest import typebridge as tb
    model = tb.parse(GROUPED_SCHEMA)
    rule = rulec.parse(NAMED_RULE)
    lean = rulec.compile_lean(rule, model, "X.Rules", "X.Schema")
    tql = rulec.compile_typeql(rule, model)
    assert '"watched" ∈ under s m.tag' in lean, lean
    # the entity is never compared to a string; its key is
    assert "has code $k1;" in tql and '$k1 == "watched";' in tql, tql
    assert '$m_tag == "watched"' not in tql, tql


@check("naming an entity whose type has no single key is refused")
def _():
    from attest import typebridge as tb
    # drop the @key: there is now no value the two forms could both compare
    assert "owns code @key," in GROUPED_SCHEMA, "the fixture moved"
    model = tb.parse(GROUPED_SCHEMA.replace("owns code @key,", "owns code,"))
    try:
        rulec.compile_lean(rulec.parse(NAMED_RULE), model, "X.R", "X.S")
    except rulec.RuleError as exc:
        assert "key" in str(exc), exc
        return
    raise AssertionError("a comparison with no agreed value was accepted")


@check("a rule can walk two hierarchies, each named at the use site")
def _():
    """More than one closure used to be refused outright whenever `is-a` was
    used, because `is-a` names no closure and BOTH compilers resolved it to
    the first one declared — wrong in the same way in both, which is exactly
    what the per-case differential cannot see. Naming the closure as the
    operator fixes it at the source. A domain with a product hierarchy AND a
    category hierarchy is an ordinary domain, not an exotic one."""
    from attest import typebridge as tb
    model = tb.parse(GROUPED_SCHEMA)
    rule = rulec.parse(TWO_CLOSURE_RULE)
    assert [s.get("closure") for s in rule["steps"] if s["kind"] == "require"] \
        == ["under", "kind-of"]
    lean = rulec.compile_lean(rule, model, "X.Rules", "X.Schema")
    tql = rulec.compile_typeql(rule, model)
    # BOTH closures are defined in Lean, not just the first — referencing one
    # that was never defined is a module that does not build
    assert "def underStep" in lean and "def kindOfStep" in lean, lean
    assert '"watched" ∈ under s m.tag' in lean, lean
    assert '"alpha" ∈ kindOf s m.tag' in lean, lean
    # and each step calls its own deployed function
    assert "_under_" in tql and "_kind_of_" in tql, tql


@check("a bare `is-a` with two closures declared is refused, and says how")
def _():
    from attest import typebridge as tb
    model = tb.parse(GROUPED_SCHEMA)
    src = TWO_CLOSURE_RULE.replace("require m.tag under watched",
                                   "require m.tag is-a watched")
    try:
        rulec.parse(src)
    except rulec.RuleError as exc:
        assert "does not say which closure" in str(exc), exc
        assert "kind-of" in str(exc), "the message should name the choices"
        return
    raise AssertionError("an ambiguous closure reference was accepted")


@check("an operator that is neither a comparison nor a closure is refused")
def _():
    src = NAMED_RULE.replace("require m.tag is-a watched",
                             "require m.tag sort-of watched")
    try:
        rulec.parse(src)
    except rulec.RuleError as exc:
        assert "neither a comparison nor a declared closure" in str(exc), exc
        return
    raise AssertionError("an unknown operator was accepted")


@check("a verdict relying on a named group cites the edges on its path")
def _():
    """`relied_facts` assumed both sides of an `is-a` were bound fields. With
    a named entity on the right it raised, so no verdict using one could be
    recorded at all — and had it not raised, the grouping facts the verdict
    rests on would have gone uncited, which is what impact analysis reads."""
    from attest import typebridge as tb
    model = tb.parse(GROUPED_SCHEMA)
    rule = rulec.parse(NAMED_RULE)
    snap = {
        "marks": [{"of": "h-1", "tag": "specific", "fact-id": "mk-1",
                   "source": "s", "recorded-at": "2026-01-01T00:00:00",
                   "retracted-at": None}],
        "groups": [
            {"child": "specific", "parent": "mid", "fact-id": "g-1",
             "source": "ref", "recorded-at": "2026-01-01T00:00:00",
             "retracted-at": None},
            {"child": "mid", "parent": "watched", "fact-id": "g-2",
             "source": "ref", "recorded-at": "2026-01-01T00:00:00",
             "retracted-at": None},
            {"child": "elsewhere", "parent": "watched", "fact-id": "g-3",
             "source": "ref", "recorded-at": "2026-01-01T00:00:00",
             "retracted-at": None},
        ],
    }
    used = rulec.relied_facts(rule, model, snap, ["mk-1"])
    assert used == ["g-1", "g-2", "mk-1"], (
        f"expected the marking and the two edges on its path, got {used}")


@check("a require comparing two literals is refused")
def _():
    lit = SAMPLE_RULE.replace("require a.item != b.item", "require a != b")
    try:
        rulec.parse(lit)
    except rulec.RuleError as exc:
        assert "literal" in str(exc)
        return
    raise AssertionError('`require a != b` compiles to `"a" ≠ "b"`, a constant')


@check("a binder spelled like a compiler-internal name is refused up front")
def _():
    # `s` is the snapshot in every Lean definition and `$t` the as-of time in
    # every TypeQL function: these failed deep in `lake build` / `define`
    for name in ("s", "t", "subject", "asof_day", "c1", "d2", "k3", "a_ra"):
        src = SAMPLE_RULE.replace(" b in ", f" {name} in ").replace(
            "b.", f"{name}.")
        try:
            rulec.parse(src)
        except rulec.RuleError as exc:
            assert "compiled forms use themselves" in str(exc), exc
            continue
        raise AssertionError(f"binder {name!r} was accepted")


# ── scoped closures, parameters, double-negation reliance ───────────
SCOPE_SCHEMA = """define
attribute fact-id,
    value string;
attribute source,
    value string;
attribute recorded-at,
    value datetime;
attribute retracted-at,
    value datetime;
attribute sample-id,
    value string;
attribute node-id,
    value string;
attribute edge-id,
    value string;
attribute crit-key,
    value string;
attribute state,
    value string @values("resolved-true", "resolved-false");
entity sample,
    owns sample-id @key,
    plays start-node:sample,
    plays open-edge:sample,
    plays resolution:sample;
entity node,
    owns node-id @key,
    plays start-node:node,
    plays goal-mark:node,
    plays open-edge:origin,
    plays open-edge:target;
entity edge-def,
    owns edge-id @key,
    plays edge-mark:edge,
    plays criterion:edge;
relation start-node,
    relates sample @card(1..1),
    relates node @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1),
    owns retracted-at @card(0..1);
relation goal-mark,
    relates node @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1),
    owns retracted-at @card(0..1);
relation open-edge,
    relates sample @card(1..1),
    relates origin @card(1..1),
    relates target @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1),
    owns retracted-at @card(0..1);
relation edge-mark,
    relates edge @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1),
    owns retracted-at @card(0..1);
relation criterion,
    relates edge @card(1..1),
    owns crit-key @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1),
    owns retracted-at @card(0..1);
relation resolution,
    relates sample @card(1..1),
    owns crit-key @card(1..1),
    owns state @card(1..1),
    owns fact-id @card(1..1),
    owns source @card(1..1),
    owns recorded-at @card(1..1),
    owns retracted-at @card(0..1);
"""

REACH_RULE = """
rule t.reaches v1
says "The goal is reachable from the start over the sample's own edges."
subject sample
parameter goal : node
collection starts : start-node for subject via sample
collection goals : goal-mark for goal via node
collection edges : open-edge for subject via sample
closure reach over edges from origin to target
conclude Reaches when
  some start-node a in starts
  some goal-mark g in goals
  require a.node reach g.node
"""

EDGE_RULE = """
rule t.edge-open v1
says "Every criterion of the edge has a resolved-true resolution."
subject sample
parameter edge : edge-def
collection marks : edge-mark for edge via edge
collection crits : criterion for edge via edge
collection resols : resolution for subject via sample
conclude EdgeOpen when
  some edge-mark m in marks
  none of
    some criterion c in crits
    none of
      some resolution v in resols
      require v.crit-key = c.crit-key
      require v.state = resolved-true
"""


@check("a closure over a scoped collection walks only the scope's edges, in both forms")
def _():
    from attest import typebridge as tb
    model = tb.parse(SCOPE_SCHEMA)
    r = rulec.parse(REACH_RULE)
    lean = rulec.compile_lean(r, model, "T.Rules", "T.Schema")
    tql = rulec.compile_typeql(r, model)
    # the Lean fold filters by the scope, and is handed the subject
    assert "e.sample == sc" in lean, lean
    assert "reachStep s.subject s.edges xs" in lean, lean
    # the TypeQL closure takes the scope and constrains every edge by it
    assert "$sc: sample" in tql and "sample: $sc)" in tql, tql
    assert "($a_node, $subject, $t)" in tql, tql


@check("a parameter is a second input in both compiled forms")
def _():
    from attest import typebridge as tb
    model = tb.parse(SCOPE_SCHEMA)
    r = rulec.parse(REACH_RULE)
    lean = rulec.compile_lean(r, model, "T.Rules", "T.Schema")
    tql = rulec.compile_typeql(r, model)
    assert "  goal : String" in lean, lean
    assert "g.node = s.goal" in lean, lean            # the binder guard
    assert "$arg0: node" in tql and "links (node: $arg0)" in tql, tql


@check("parameters are validated: undeclared scope, collisions, reserved binders")
def _():
    bad = [
        REACH_RULE.replace("for goal via node", "for target via node"),
        REACH_RULE.replace("parameter goal : node",
                           "parameter goal : node\nparameter goal : node"),
        REACH_RULE.replace("parameter goal : node", "parameter edges : node"),
        REACH_RULE.replace("some start-node a in starts",
                           "some start-node arg0 in starts").replace(
                               "require a.node", "require arg0.node"),
    ]
    for src in bad:
        try:
            rulec.parse(src)
        except rulec.RuleError:
            continue
        raise AssertionError(f"accepted:\n{src}")


@check("a rule over global facts only gives its search a use of $subject")
def _():
    from attest import typebridge as tb
    model = tb.parse(SCOPE_SCHEMA)
    r = rulec.parse("""
rule t.any-goal v1
says "Some goal is marked."
subject sample
collection goals : goal-mark
conclude AnyGoal when
  some goal-mark g in goals
""")
    tql = rulec.compile_typeql(r, model)
    assert "$subject isa sample;" in tql, tql


@check("facts read under two negations are relied on; under one they are not")
def _():
    r = rulec.parse(EDGE_RULE)
    assert rulec.double_negated_collections(r) == ["resols"]
    rows = {
        "marks": [{"edge": "e1", "fact-id": "mk", "retracted-at": None}],
        "crits": [{"edge": "e1", "crit-key": "a", "fact-id": "cr",
                   "retracted-at": None}],
        "resols": [{"sample": "A", "crit-key": "a", "state": "resolved-true",
                    "fact-id": "rs", "retracted-at": None}],
    }
    used = rulec.relied_facts(r, None, rows, ["mk"],
                              scopes={"subject": "A", "edge": "e1"})
    assert "rs" in used, used          # the double-negated support
    assert "cr" not in used, used      # single negation: retraction cannot flip it


@check("a scoped closure path is traced over the scope's own edges")
def _():
    r = rulec.parse(REACH_RULE)
    rows = {
        "starts": [{"sample": "A", "node": "n0", "fact-id": "st"}],
        "goals": [{"node": "n2", "fact-id": "g2"}],
        "edges": [{"sample": "A", "origin": "n0", "target": "n1",
                   "fact-id": "a01", "retracted-at": None},
                  {"sample": "A", "origin": "n1", "target": "n2",
                   "fact-id": "a12", "retracted-at": None},
                  {"sample": "B", "origin": "n0", "target": "n2",
                   "fact-id": "b02", "retracted-at": None}],
    }
    used = rulec.relied_facts(r, None, rows, ["st", "g2"],
                              scopes={"subject": "A", "goal": "n2"})
    assert {"a01", "a12"} <= set(used) and "b02" not in used, used


@check("an axiom-free proof has an axioms report too")
def _():
    from attest.kernel import axiom_reports
    log = ("'C.holds' does not depend on any axioms\n"
           "'D.fails' depends on axioms: [propext,\n Quot.sound]\n")
    assert axiom_reports(log) == [("C.holds", set()),
                                  ("D.fails", {"propext", "Quot.sound"})]


@check("a snapshot without parameters keeps its hash; with them the hash covers them")
def _():
    from attest import make_snapshot
    a = make_snapshot("A", "2026-10-01T00:00:00", {"x": []})
    b = make_snapshot("A", "2026-10-01T00:00:00", {"x": []}, params={})
    c = make_snapshot("A", "2026-10-01T00:00:00", {"x": []}, params={"goal": "n1"})
    d = make_snapshot("A", "2026-10-01T00:00:00", {"x": []}, params={"goal": "n2"})
    assert a.sha256 == b.sha256 and a.params == ()
    assert len({a.sha256, c.sha256, d.sha256}) == 3
    assert c.params == (("goal", "n1"),)


# ── 7. configuration ────────────────────────────────────────────────
@check("an https endpoint implies TLS and gets port alternatives")
def _():
    config = StoreConfig(address="https://host.example:80", tls=True)
    candidates = config.candidates()
    assert candidates[0] == "https://host.example:80"
    assert "https://host.example:443" in candidates
    plain = StoreConfig(address="127.0.0.1:1729", tls=False)
    assert plain.candidates() == ["127.0.0.1:1729"]


# ── 8. the review of 2026-10-22 ─────────────────────────────────────
# One test per finding. Each of these passed review as "valid" and each had
# no coverage at all, which is why it survived.


def _rule(body, header="rule demo.x v0.1"):
    return (f"{header}\nsays \"t\"\n\nsubject item\n\n"
            f"collection rows : row for subject via item\n\n"
            f"conclude Flagged when\n  some row m in rows\n{body}\n")


@check("a # inside a rule value is part of the value, not a comment")
def _():
    r = rulec.parse(_rule('  require m.source = "ICD#10"   # trailing'))
    assert r["steps"][1]["rhs"] == '"ICD#10"', r["steps"][1]["rhs"]


@check("a value with an unbalanced quote is refused, not emitted verbatim")
def _():
    # `"a"b"` parsed clean and went into BOTH compiled forms, where the
    # stray quote ends the literal early.
    try:
        rulec.parse(_rule('  require m.source = "a"b"'))
    except rulec.RuleError:
        return
    raise AssertionError("an unbalanced literal was accepted")


@check("a rule version cannot carry a Lean comment delimiter")
def _():
    # `-/` closed the generated module's header comment, and the rest was
    # elaborated as Lean — reaching `initialize`, i.e. code at build time.
    try:
        rulec.parse(_rule('  require m.source = "x"',
                          header='rule demo.x v0.1"++"-/initialize'))
    except rulec.RuleError:
        return
    raise AssertionError("an injecting version string was accepted")


@check("a rule id must be dot-separated identifiers")
def _():
    for bad in ("demo..x", "demo.x/y", "1demo"):
        try:
            rulec.parse(_rule('  require m.source = "x"',
                              header=f"rule {bad} v0.1"))
        except rulec.RuleError:
            continue
        raise AssertionError(f"rule id {bad!r} was accepted")


@check("every fixture rule still parses after the name validation")
def _():
    root = pathlib.Path(__file__).resolve().parent / "fixtures" / "rules"
    files = sorted(root.rglob("*.rule"))
    assert files, "no rule files found"
    for path in files:
        rulec.parse(path.read_text())


@check("a char literal cannot hide a forbidden construct from the denylist")
def _():
    from attest.kernel import forbidden
    quote, tick = chr(34), chr(39)
    # `'"'` was read as the START of a string literal, so everything up to
    # the next real quote was blanked — including a set_option that turns
    # the kernel off entirely.
    hidden = (f"def c : Char := {tick}{quote}{tick}\n"
              f"set_option debug.skipKernelTC true in\n"
              f"theorem t : False := by sorry\n"
              f"def l : String := {quote}x{quote}\n")
    assert forbidden(hidden) == "set_option", forbidden(hidden)
    # and a value that merely spells a keyword is still data
    assert forbidden(f"def l : String := {quote}set_option elab{quote}\n") is None
    assert forbidden(f"def c : Char := {tick}a{tick}\n") is None


@check("ledger times compare as instants, not as text")
def _():
    from attest import instant
    # The same instant written to different precision. As text the shorter
    # form is a prefix and therefore sorts STRICTLY EARLIER, so a
    # lexicographic `mark >= at` reads "the window is still open" about a
    # mark that is in fact exactly at the as-of.
    same = ("2026-10-01T00:00:00.1", "2026-10-01T00:00:00.10")
    assert instant(same[0]) == instant(same[1])
    assert same[0] < same[1], "text comparison disagrees, which is the point"
    for pair in (("2026-10-01T00:00:00", "2026-10-01T00:00:00.000000"),):
        assert instant(pair[0]) == instant(pair[1])
    # and real ordering still holds
    assert instant("2026-10-01T00:00:00.9") > instant("2026-10-01T00:00:00.10")


@check("a decision seals the as-of window before reading the snapshot")
def _():
    from attest import seal_window
    # Mark behind the as-of: the window is open, so a writer whose clock
    # reads between the two could still land inside an already-certified
    # snapshot. Sealing closes it.
    store = FakeStore(rows=[{"h": "2026-10-01T00:00:00"}])
    assert seal_window(store, "2026-10-10T00:00:00") == "2026-10-10T00:00:00"
    assert store.written and "high-water" in store.written[0]
    assert store.must_affect, "the advance must be a compare-and-set"
    # Mark already past the as-of: nothing to do, and nothing written.
    ahead = FakeStore(rows=[{"h": "2026-10-20T00:00:00"}])
    seal_window(ahead, "2026-10-10T00:00:00")
    assert not ahead.written, ahead.written


@check("artifacts are keyed by id, so two of one kind both survive")
def _():
    from attest import typebridge
    import tempfile, os
    store = FakeStore(rows=[{"a": "x"}])          # "already published"
    with tempfile.TemporaryDirectory() as d:
        paths = []
        for i in (1, 2):
            path = os.path.join(d, f"T{i}.lean")
            with open(path, "w") as handle:
                handle.write(f"-- theorem module {i}\n")
            paths.append(path)
        ids = typebridge.publish(
            store, [(f"Acme.T{i}", "theorems", p)
                    for i, p in enumerate(paths, 1)], "2026-10-01T00:00:00")
    # Keyed by kind this was a single entry and one module was lost.
    assert len(ids) == 2, ids
    assert set(ids.values()) == {"theorems"}, ids


@check("lookup catches a dropped fact and a duplicated row together")
def _():
    from attest.store import SnapshotIncomplete
    # The two faults used to CANCEL: one fact missing a required attribute
    # (absent from the attributed query) plus one whose attribute pattern
    # multiplied into two rows gives equal counts, and both passed. Compared
    # as multisets of fact ids, each is named separately.
    class Stub(Store):
        def __init__(self, full, bare):
            self.full, self.bare = full, bare

        def _rows(self, tx, query):
            return self.full if "has source" in query else self.bare

    key = "probe_fid_"
    bare = [{key: "f1"}, {key: "f2"}]
    # f1 dropped (no source) and f2 duplicated: two rows either way
    full = [{key: "f2", "s": "a"}, {key: "f2", "s": "b"}]
    try:
        Stub(full, bare).lookup(None, "$r isa thing;", "$r has source $s;",
                                "$s", "$r")
    except SnapshotIncomplete as exc:
        assert "f1" in str(exc) or "f2" in str(exc), str(exc)
    else:
        raise AssertionError("the cancelling pair passed unnoticed")
    # the clean case returns rows without the probe column, so the snapshot
    # hash is unaffected by the identity check
    ok = Stub([{key: "f1", "s": "a"}, {key: "f2", "s": "b"}], bare)
    rows = ok.lookup(None, "$r isa thing;", "$r has source $s;", "$s", "$r")
    assert rows == [{"s": "a"}, {"s": "b"}], rows


@check("a rule with BOTH parameters and as-of-day binds both in the search")
def _():
    from attest import search
    # `extra = ...` instead of `+=` discarded the parameter bindings, so the
    # generated query called the function with $a0 never bound. Neither the
    # parameters change nor the as-of change covered the combination.
    rule = rulec.parse(
        'rule demo.both v0.1\nsays "t"\n\nsubject item\n'
        'parameter goal : marker\n\n'
        'collection rows : row for subject via item\n\n'
        'conclude Flagged when\n  some row m in rows\n'
        '  require m.taken >= as-of-day - 180\n')
    assert rule["params"] and rulec.uses_as_of(rule)
    store = FakeStore(rows=[])
    model = {"types": {"marker": {"owns": [{"attr": "code", "key": True}],
                                  "plays": []}},
             "attributes": {"code": {"value": "string"}}}
    search(store, rule, "i-1", "item", "iid", "2026-10-10T00:00:00",
           params={"goal": "g-1"}, model=model)
    query = store.queried[-1]
    assert '$a0 isa marker' in query, query
    assert 'has code "g-1"' in query, query
    assert "let $d =" in query, query
    assert "$a0, $t, $d" in query or "$a0, $t," in query, query


@check("retract reports a write conflict as a conflict, not as missing data")
def _():
    from attest.store import ConcurrentWrite, WriteMatchedNothing
    class Conflicting(Store):
        def __init__(self, exc):
            self.exc = exc
        def rows(self, query, tx=None):
            return [{"h": "2026-10-05T00:00:00"}]
        def write(self, queries, kind=None, *, must_affect=False):
            raise self.exc
    # A commit-time conflict says "another writer committed a conflicting
    # change" — no "ledger moved" in it — and used to be reported as
    # "already retracted, or does not exist": a concurrency problem dressed
    # as a statement about the caller's data.
    try:
        Ingest(Conflicting(ConcurrentWrite("another writer committed"))).retract("f1")
    except ConcurrentWrite:
        pass
    else:
        raise AssertionError("a write conflict was swallowed")
    # a genuine no-match still reads as a statement about the data
    try:
        Ingest(Conflicting(WriteMatchedNothing(1, "q"))).retract("f1")
    except VerificationError as exc:
        assert "already retracted" in str(exc), str(exc)


# ── must-fail corpus ───────────────────────────────────────────────
MUST_FAIL = pathlib.Path(__file__).resolve().parent / "must_fail"


def _header(text, key, prefix):
    for line in text.splitlines():
        if line.startswith(f"{prefix} {key}:"):
            return line.split(":", 1)[1].strip()
    return None


@check("every rule in the must-fail corpus is refused, with its own error")
def _():
    from attest import typebridge
    model = typebridge.parse(SAMPLE_SCHEMA)
    files = sorted((MUST_FAIL / "rules").glob("*.rule"))
    assert files, "the corpus is empty"
    for path in files:
        text = path.read_text()
        expect = _header(text, "expect", "#")
        assert expect, f"{path.name}: no `# expect:` header"
        try:
            rule = rulec.parse(text)
            if _header(text, "stage", "#") == "compile":
                rulec.compile_lean(rule, model, "Demo.Rules", "Demo.Schema")
                rulec.compile_typeql(rule, model)
        except (rulec.RuleError, typebridge.UnsupportedSchema) as exc:
            assert expect in str(exc), (
                f"{path.name}: refused, but for the wrong reason: {exc}")
        else:
            raise AssertionError(f"{path.name}: accepted")


@check("every Lean file in the must-fail corpus trips the denylist")
def _():
    from attest.kernel import forbidden
    files = sorted((MUST_FAIL / "lean").glob("*.lean"))
    assert files, "the corpus is empty"
    for path in files:
        text = path.read_text()
        expect = _header(text, "expect", "--")
        assert expect, f"{path.name}: no `-- expect:` header"
        # the header comments name the construct, so they are not scanned
        body = "\n".join(l for l in text.splitlines()
                         if not l.startswith("--"))
        found = forbidden(body)
        assert found == expect, f"{path.name}: found {found!r}, want {expect!r}"


# ── compiler outputs that are stored, and must not move ─────────────
@check("the compiler reproduces every committed Lean module and golden output")
def _():
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    import golden
    problems = golden.compare()
    assert not problems, "\n".join(problems[:10])


@check("the case file decide stores and recheck regenerates has one format")
def _():
    from attest import runner, typebridge
    from attest.domain import LeanPackage
    model = typebridge.parse(SAMPLE_SCHEMA)
    rule = rulec.parse(THRESHOLD_RULE)
    snap = make_snapshot("h1", "2026-10-10T00:00:00", {"readings": [
        {"fact-id": "f1", "of": "h1", "source": "s",
         "recorded-at": "2026-01-01T00:00:00", "test-code": "a",
         "reading": 71, "taken": 20000, "note": None}]})
    lean = LeanPackage(pathlib.Path("/x"), "Demo", "Demo.Schema", "Demo.Rules")
    case = runner.case_file(snap, model, rule, lean)
    # Byte for byte what both paths produced before they shared a builder;
    # every stored proof has to keep regenerating to exactly this.
    assert case.source("holds", case.positive, "by decide") == (
        'import Demo.Rules.Demo.Threshold\nopen Demo.Schema\n'
        'open Demo.Rules.Demo.Threshold\n\nnamespace Case_9823e2c93ff6\n'
        'def snap : Snapshot :=\n  { readings := [\n    { of := "h1", '
        'factId := "f1", note := none, reading := 71, recordedAt := '
        '"2026-01-01T00:00:00", source := "s", taken := 20000, testCode := '
        '.a }],\n    subject := "h1" }\nexample : (OverLimit snap) ↔ '
        '(Demo.Rules.Demo.Threshold.OverLimit snap) := Iff.rfl\n\n'
        'theorem holds : OverLimit snap :=\n  by decide\n\n'
        'end Case_9823e2c93ff6\n#print axioms Case_9823e2c93ff6.holds\n')
    assert case.negative == "¬ (OverLimit snap)"


# ── the resolved IR: one reading of a rule for both compiled forms ──
_WALK_SCHEMA = SAMPLE_SCHEMA.replace(
    "owns holder-id @key;", "owns holder-id @key,\n    plays measurement:of;")


@check("an undeclared enum value is refused by BOTH compilers, not only Lean")
def _():
    from attest import typebridge
    model = typebridge.parse(SAMPLE_SCHEMA)
    rule = rulec.parse(THRESHOLD_RULE.replace("m.test-code = a",
                                              "m.test-code = z"))
    # The check lived inside the Lean generator, so the TypeQL search for
    # this rule compiled — and `sync` deploys the search before it compiles
    # the Lean rule.
    for compile_ in (lambda: rulec.compile_typeql(rule, model),
                     lambda: rulec.compile_lean(rule, model, "D.R", "D.S")):
        try:
            compile_()
        except rulec.RuleError as exc:
            assert "is not one of the values" in str(exc), str(exc)
        else:
            raise AssertionError("an undeclared enum value compiled")


@check("a walk from an attribute is refused by both compilers")
def _():
    from attest import typebridge
    model = typebridge.parse(_WALK_SCHEMA)
    rule = rulec.parse("""
rule demo.walk v0.1
says "x"
subject holder
collection readings : measurement for subject via of
closure up over readings from of to of
conclude Hit when
  some measurement m in readings
  require m.source up m.source
""")
    # Both used to compile it. In Lean an attribute's string was walked as
    # if it were an entity key; in TypeQL the closure was handed an
    # attribute where it takes an entity. Two different meanings.
    for compile_ in (lambda: rulec.compile_typeql(rule, model),
                     lambda: rulec.compile_lean(rule, model, "D.R", "D.S")):
        try:
            compile_()
        except rulec.RuleError as exc:
            assert "an attribute, not a role" in str(exc), str(exc)
        else:
            raise AssertionError("a walk from an attribute compiled")


@check("the IR records witness positions and what a negation reads")
def _():
    from attest import typebridge
    ir = rulec.resolve(rulec.parse(LATEST_RULE), typebridge.parse(SAMPLE_SCHEMA))
    assert [type(s).__name__ for s in ir.steps] == ["Some", "Require", "NoneOf"]
    # `n` is bound inside the negation and cited nowhere; `m` is read there
    assert {v: b.witness for v, b in ir.binders.items()} == {"m": 0, "n": None}
    assert ir.steps[2].free == frozenset({"m"})
    assert ir.binders["n"].depth == 1


# ── what each kernel attempt actually did ───────────────────────────
def _attempt(outcome, reason=None):
    return Check(theorem="Case_x.holds", name="holds", statement="C snap",
                 proof="p", accepted=outcome == "proved", axioms=(),
                 reason=reason, file="", outcome=outcome)


@check("a kernel check that did not run is told apart from a rejection")
def _():
    # an unbuilt package: Lean never ran
    kernel = Kernel(pathlib.Path("/nonexistent"), case_dir=pathlib.Path("/tmp"))
    result = kernel.check("Case_x", ["M"], [], "", "holds", "True", "trivial")
    assert result.outcome == "not-run" and not result.ran, result
    # a forbidden construct: refused before Lean saw it
    result = kernel.check("Case_x", ["M"], [], "set_option x true in\n",
                          "holds", "True", "trivial")
    assert result.outcome == "refused" and not result.ran, result
    # the outcome is part of what the certificate records
    assert result.as_dict()["outcome"] == "refused"
    # and an outcome that contradicts `accepted` cannot be built
    try:
        Check(theorem="t", name="t", statement="", proof="", accepted=True,
              axioms=(), reason=None, file="", outcome="refuted")
    except ValueError:
        pass
    else:
        raise AssertionError("an accepted check claimed to be refuted")


@check("a witness the kernel never finished checking is not a disagreement")
def _():
    from attest.runner import _differential
    timed_out = _attempt("not-run", "kernel check did not complete: Timeout")
    refuted = _attempt("refuted", "type mismatch")
    proved = _attempt("proved")
    # the case that used to be misreported: the witness check timed out,
    # the kernel then proved C by evaluation — search and kernel AGREE
    d = _differential("C", "C", [["f1"]], False, timed_out,
                      [timed_out, _attempt("refuted"), proved])
    assert d.startswith("agree"), d
    assert "not checked" in d and "not-run" in d, d
    # a witness the kernel did reject is still a disagreement
    d = _differential("C", "C", [["f1"]], False, refuted,
                      [refuted, _attempt("refuted"), proved])
    assert d.startswith("DISAGREE") and "rejected by the kernel" in d, d
    # the kernel proving the negation contradicts any witness — but the
    # wording no longer claims a rejection that was never observed
    d = _differential("not C", "C", [["f1"]], False, timed_out,
                      [timed_out, proved])
    assert d.startswith("DISAGREE") and "did not finish" in d, d
    assert "rejected" not in d, d
    # no verdict because nothing ran is a retry, not a refusal of the rule
    d = _differential("ERROR", "C", [], False, None,
                      [_attempt("not-run", "build failed")] * 2)
    assert "did not finish" in d and "retrying" in d, d
    d = _differential("ERROR", "C", [], False, None,
                      [_attempt("refuted"), _attempt("refuted")])
    assert "settled neither" in d, d
    # one attempt timing out is enough for a retry to be worth it
    d = _differential("ERROR", "C", [], False, None,
                      [_attempt("refuted"), _attempt("not-run", "Timeout")])
    assert "retrying" in d, d
    # unchanged: a found witness the kernel accepted, and silence on a fail
    assert _differential("C", "C", [["f1"]], True, proved, [proved]) == "agree"
    assert _differential("not C", "C", [], False, None, [proved]) == "agree"
    assert _differential("C", "C", [], False, None,
                         [_attempt("refuted"), proved]).startswith("DISAGREE")


# ── polarity: which changes can flip which verdict ──────────────────
def _fixture_rules():
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    import golden
    return list(golden.rules())


@check("polarity predicts every verdict flip, on random snapshots of every fixture rule")
def _():
    import random
    from refeval import add, drop, random_case
    flips = 0
    for label, rule, model, _lean, _root in _fixture_rules():
        sens = rulec.sensitivity(rule)
        for seed in range(40):
            rng = random.Random(seed)
            case = random_case(rule, model, rng)
            verdict = "holds" if case.holds() else "fails"
            where = {r["fact-id"]: name for name, rows in case.data.items()
                     for r in rows}
            relied = (set(rulec.relied_facts(rule, model, case.data,
                                             list(case.witnesses()[0]),
                                             scopes=case.scopes))
                      if verdict == "holds" else None)
            for fid, coll in where.items():
                if drop(case, fid).holds() == (verdict == "holds"):
                    continue
                flips += 1
                # a retraction that flips the verdict comes from a
                # collection the table names for it ...
                assert coll in sens[verdict]["retract"], (
                    f"{label} seed {seed}: retracting {fid} ({coll}) flipped "
                    f"{verdict}, but polarity says it cannot")
                # ... and, for a holding verdict, is a fact it relied on
                if relied is not None:
                    assert fid in relied, (
                        f"{label} seed {seed}: retracting {fid} flipped the "
                        f"verdict but it is not among the relied-on facts")
            for coll in case.data:
                bigger = add(case, coll, random.Random(seed * 1000 + 7))
                if bigger.holds() != (verdict == "holds"):
                    flips += 1
                    assert coll in sens[verdict]["add"], (
                        f"{label} seed {seed}: adding to {coll} flipped "
                        f"{verdict}, but polarity says it cannot")
    # the property is vacuous if nothing ever flipped
    assert flips > 50, f"only {flips} flips observed"


@check("polarity gives double negation its old meaning, and anchors are derived")
def _():
    from attest import typebridge
    rule = rulec.parse(LATEST_RULE)
    assert rulec.polarity(rule) == {"readings": frozenset({0, 1})}
    assert rulec.sensitivity(rule) == {
        "holds": {"retract": ["readings"], "add": ["readings"]},
        "fails": {"retract": ["readings"], "add": ["readings"]}}
    # the scoped collection's own role is the anchor, in the canonical form
    anchors = rulec.scope_anchors(rule, typebridge.parse(SAMPLE_SCHEMA))
    assert anchors == ('$f isa measurement, has fact-id "{fid}", '
                       'links (of: $x); coverage (decision: $d, item: $x);',)
    # and a hand-written pattern is recognised whatever its variable is
    assert rulec.anchor_key(anchors[0].replace("$f", "$e")) == (
        "measurement", "of")


@check("derived anchors are the ones each fixture rule implies")
def _():
    import types
    from attest import runner
    # What a domain would otherwise write by hand: a scoped collection is
    # about its `via` role's player, a closure's collection about the node a
    # walk starts from, and a global collection joined by `=` or a walk about
    # the entity on the joined role.
    want = {
        "any-listing": set(),
        "blocked": {("engagement", "holder"), ("ownership", "owned"),
                    ("listing", "party")},
        "complete": {("item-mark", "item"), ("criterion", "item"),
                     ("resolution", "holder")},
        "in-group": {("claim", "holder"), ("code-isa", "child")},
        "latest-high": {("reading", "holder")},
        "reaches": {("start-node", "holder"), ("goal-mark", "node"),
                    ("open-edge", "holder"), ("open-edge", "origin")},
        "two-parties": {("engagement", "holder")},
    }
    blind = {}
    for label, rule, model, _lean, _root in _fixture_rules():
        name = pathlib.Path(label).stem
        derived = {rulec.anchor_key(a) for a in rulec.scope_anchors(rule, model)}
        assert derived == want[name], f"{name}: {sorted(derived)}"
        ns = types.SimpleNamespace(rule_path=None, scope_anchors=())
        gap = runner.unanchored(model, ns, rule)
        if gap:
            blind[name] = gap
    # Exactly one blind spot is left, and it is real: `any-listing` reads a
    # global collection through no role at all, so a listing recorded later
    # can flag no earlier decision. `sync` warns about it.
    assert blind == {"any-listing": ["listing"]}, blind


# ── the review of 2026-10-23 ─────────────────────────────────────────


@check("a deployed function does not stop a past decision re-verifying")
def _():
    from attest import typebridge
    # `render` embeds a hash of types AND functions, and recheck compared
    # whole files — so one more deployed function (sync deploys one per
    # rule, named by the rule's hash) made every earlier decision report
    # that the schema it cites no longer renders. `types_match` reuses the
    # stored file's own hash line, so only a real type change shows.
    import copy
    import re
    import schema_offline
    fixtures = pathlib.Path(__file__).resolve().parent / "fixtures"
    model = schema_offline.model(fixtures / "schema.tql")
    stored = typebridge._render(model, "a" * 64, "Acme.Schema")
    # the whole-schema hash really is part of the file, which is why
    # comparing whole files answered the wrong question
    assert typebridge._render(model, "b" * 64, "Acme.Schema") != stored
    m = re.search(r'def schemaSha256 : String := "([0-9a-f]{64})"', stored)
    assert m and m.group(1) == "a" * 64
    # reusing the stored hash makes the comparison about TYPES only, so a
    # newly deployed function — which moves the hash and nothing else — no
    # longer looks like a changed schema
    assert typebridge._render(model, m.group(1), "Acme.Schema") == stored
    # and a real type change is still caught
    moved = copy.deepcopy(model)
    victim = next(n for n, ty in moved["types"].items()
                  if ty.get("sub") == "fact" and ty["owns"])
    moved["types"][victim]["owns"].pop()
    assert typebridge._render(moved, m.group(1), "Acme.Schema") != stored


@check("a sealed window does not make every other writer a backdater")
def _():
    # A decision closes its as-of window by advancing the mark. Judging
    # backdating against that mark made one machine's clock everyone's
    # problem: a decider running fast refused every other writer, with
    # correct clocks, until real time caught up. A tolerance constant only
    # narrowed the window in which that happened; the mark is simply the
    # wrong thing to judge against.
    sealed = LedgerStore(mark="2026-10-01T02:00:00",      # seal, 2h ahead
                         last_fact="2026-10-01T00:00:00")  # real facts
    stamp = Ingest(sealed, clock=lambda: "2026-10-01T00:00:30").now()
    assert stamp > "2026-10-01T02:00:00", stamp   # steps past the seal
    # going behind a fact that already exists is still refused, at any
    # distance, with no constant involved
    behind = LedgerStore(mark="2026-10-01T02:00:00",
                         last_fact="2026-10-01T00:01:00")
    try:
        Ingest(behind, clock=lambda: "2026-10-01T00:00:30").now()
    except ValueError as exc:
        assert "before the last recorded fact" in str(exc), str(exc)
    else:
        raise AssertionError("a write behind an existing fact was accepted")


@check("sealing the window reports a lost race as retryable")
def _():
    from attest.store import ConcurrentWrite, WriteMatchedNothing, seal_window
    # It wrote directly, so a lost compare-and-set surfaced as "a query
    # matched nothing" — a concurrency problem reported as a statement
    # about the caller's data, the same confusion `retract` had.
    class Racing(Store):
        def __init__(self): self.mark = "2026-10-01T00:00:00"
        def rows(self, query, tx=None): return [{"h": self.mark}]
        def write(self, queries, kind=None, *, must_affect=False):
            raise WriteMatchedNothing(0, "advance")
    try:
        seal_window(Racing(), "2026-10-10T00:00:00")
    except ConcurrentWrite as exc:
        assert "Retry" in str(exc), str(exc)
    else:
        raise AssertionError("a lost race was not reported as retryable")


@check("an anchor whose player is never recorded as covered is not coverage")
def _():
    import types as _t
    import schema_offline
    from attest import runner
    # An anchor fires by joining its role's player to a `coverage` edge, so
    # it is inert unless the export records that player. Counting anchors by
    # type called the collection covered anyway.
    fixtures = pathlib.Path(__file__).resolve().parent / "fixtures"
    model = schema_offline.model(fixtures / "schema.tql")
    rule = rulec.load(fixtures / "rules" / "in-group.rule")
    patterns = rulec.scope_anchors(rule, model)
    keys = {k for k in map(rulec.anchor_key, patterns) if k}
    assert keys == {("claim", "holder"), ("code-isa", "child")}, sorted(keys)
    # an export that records only the holder: the code hierarchy's anchor
    # binds a code, which nothing records, so it can never fire
    usable = set(runner.usable_anchors(model, patterns, {"holder"}))
    assert usable == {("claim", "holder")}, sorted(usable)
    # with no covered set given, every parsed anchor counts — which is all
    # the old check ever proved
    assert set(runner.usable_anchors(model, patterns)) == keys
    # and the blind spot is then reported, not hidden
    ns = _t.SimpleNamespace(rule_path=None, scope_anchors=())
    assert runner.unanchored(model, ns, rule, covered_types={"holder"}) == \
        ["code-isa"]


@check("a role played by a subtype of a recorded type is covered")
def _():
    import schema_offline
    from attest import runner
    # The export may record a parent type (`party`) where the anchor binds a
    # child (`firm`); the coverage edge is on the same instance either way.
    fixtures = pathlib.Path(__file__).resolve().parent / "fixtures"
    model = schema_offline.model(fixtures / "schema.tql")
    rule = rulec.load(fixtures / "rules" / "blocked.rule")
    patterns = rulec.scope_anchors(rule, model)
    usable = set(runner.usable_anchors(model, patterns, {"holder", "party"}))
    assert ("ownership", "owned") in usable, sorted(usable)        # firm
    assert ("listing", "party") in usable, sorted(usable)          # party
    assert ("engagement", "holder") in usable, sorted(usable)


@check("the coverage check does not depend on how anchors are listed")
def _():
    import types as _t
    import schema_offline
    from attest import runner
    # It inspected only the FIRST pattern naming a type, so the same domain
    # read covered or uncovered after a harmless reordering.
    fixtures = pathlib.Path(__file__).resolve().parent / "fixtures"
    model = schema_offline.model(fixtures / "schema.tql")
    rule = rulec.load(fixtures / "rules" / "blocked.rule")
    odd = ('$e isa ownership, has fact-id "{fid}", links (owned: $x),'
           ' links (owner: $y); coverage (decision: $d, item: $y);')
    parseable = ('$e isa ownership, has fact-id "{fid}",'
                 ' links (owned: $x); coverage (decision: $d, item: $x);')
    one = _t.SimpleNamespace(rule_path=None, scope_anchors=(odd, parseable))
    two = _t.SimpleNamespace(rule_path=None, scope_anchors=(parseable, odd))
    for covered in (None, {"holder"}):
        assert runner.unanchored(model, one, rule, covered_types=covered) == \
            runner.unanchored(model, two, rule, covered_types=covered), \
            "order changed the answer"


@check("a recheck record carries no machine-local path")
def _():
    # `workspace` is a temp directory that changes every run, and it was
    # being serialised into committed output — a diff on every run.
    r = Recheck("dec-1", "C", True, None, {"a@1": "rule-source"},
                workspace="/var/folders/xx/attest-recheck-abc")
    assert "workspace" not in r.as_dict(), r.as_dict()
    assert r.workspace, "still available on the object itself"
    assert not any("/var/folders" in str(v) for v in r.as_dict().values())


if __name__ == "__main__":
    for name in PASS:
        print(f"  pass  {name}")
    for name, why in FAIL:
        print(f"  FAIL  {name}\n          {why}")
    print(f"\n{len(PASS)}/{len(PASS) + len(FAIL)} passed")
    sys.exit(1 if FAIL else 0)
