"""The fact store: a connection, validated writes, and as-of reads.

Three things here are load-bearing and were learned the hard way.

**Ledger time is stamped, never supplied.** :class:`Ingest` is the only write
path for facts. It takes the time from a clock and refuses to move the ledger
backwards, because a fact recorded before an existing one would change a
snapshot that has already been decided and certified.

**An export runs in one read transaction.** Otherwise a write landing between
two lookups produces a snapshot that never existed, and its hash certifies it.

**A lookup proves it dropped nothing.** :meth:`Store.lookup` runs each query
twice — once selecting the attributes being exported, once selecting only the
fact — and compares the counts. A fact lacking a required attribute would
otherwise vanish from the export rather than failing it.
"""

from __future__ import annotations

import collections
import datetime
import pathlib
import re
from typing import Any

from .config import StoreConfig

CORE_SCHEMA = pathlib.Path(__file__).resolve().parent / "core.tql"

#: identifiers that may be interpolated into a query
_IDENT = re.compile(r"^[A-Za-z0-9_.:@+-]{1,128}$")
_DATETIME = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d{1,9})?$")


class VerificationError(Exception):
    """The arrangement refused to produce a verdict."""


def _trim(value) -> str:
    """A ledger time as stored, keeping sub-second precision if present."""
    text = str(value).replace("Z", "").split("+")[0].rstrip()
    return text.rstrip("0").rstrip(".") if "." in text else text


class ConcurrentWrite(VerificationError):
    """Another writer committed a conflicting change. Retry."""


class WriteMatchedNothing(VerificationError):
    """A write's `match` found nothing, so the whole transaction was aborted.

    Carries the **index** of the offending query within the batch, because a
    caller that wraps its own queries with ones of its own — as `Ingest`
    does with the ledger advance — has to tell them apart to report the
    failure honestly.

    The index exists because the first version discriminated on message
    text: `Ingest.record` tested ``advance[:60] in str(exc)`` and worked
    only because this raise embedded ``query[:90]``. Two constants in two
    functions, silently coupled; shortening either one would have turned a
    lost compare-and-set into "your data is missing" and retry logic would
    have stopped retrying.
    """

    def __init__(self, index: int, query: str) -> None:
        super().__init__(f"write matched nothing, aborted: {query[:90]}…")
        self.index = index
        self.query = query


class SnapshotIncomplete(VerificationError):
    """An export dropped a fact that lacked a required attribute."""


class UnknownSubject(VerificationError):
    """A decision was asked about a subject the store has never heard of.

    The empty snapshot that would otherwise be produced is not an honest
    answer: any rule whose conclusion requires finding something is refuted
    by the empty snapshot, so an unknown subject would be decided — and
    decided in the reassuring direction. Absence of a subject and absence of
    what the rule looks for are different facts.
    """


def ident(value: str) -> str:
    """An identifier safe to interpolate. Anything else is refused."""
    text = str(value)
    if not _IDENT.match(text):
        raise ValueError(f"unsafe identifier: {value!r}")
    return text


def dt(value: str) -> str:
    """An ISO-8601 datetime, to the second. Anything else is refused.

    The shape is checked *and* the date is parsed. A regex alone accepts
    month 13 and day 32, which TypeDB would then reject at query time with a
    syntax error rather than here with a useful one.
    """
    text = str(value).replace("Z", "").split("+")[0].rstrip()
    if not _DATETIME.match(text):
        raise ValueError(f"not an ISO-8601 datetime: {value!r}")
    try:
        datetime.datetime.strptime(text.split(".")[0], "%Y-%m-%dT%H:%M:%S")
    except ValueError as exc:
        raise ValueError(f"not a real datetime: {value!r} ({exc})") from None
    return text


def instant(value: str) -> datetime.datetime:
    """A ledger time as a comparable instant.

    Parsed rather than compared as text: ISO-8601 strings with differing
    numbers of fractional digits do not order lexicographically, so `.9`
    sorts after `.10`.
    """
    return datetime.datetime.fromisoformat(_trim(value).replace(" ", "T"))


def seal_window(store, at: str) -> str:
    """Close the as-of window at `at`, so nothing can land inside it later.

    A snapshot asks for the facts whose `recorded-at` is at or before `at`.
    That set is only frozen — and the certificate's hash only reproducible —
    if no future write can be stamped at or before `at`. The ledger is
    strictly monotonic and refuses to move backwards, so the condition is
    exactly `high-water >= at`.

    Nothing established it. `decide` refused only an as-of later than its
    own wall clock, which leaves the whole gap between the last recorded
    fact and the decision's date open: with the mark at the 1st and a
    decision as of the 10th, a writer whose clock read the 3rd was accepted
    and its fact landed inside a snapshot already certified and signed off.
    Clock skew between machines widens the same hole.

    So the window is closed before the snapshot is read, by advancing the
    mark to `at` if it is behind. Advancing is truthful — `decide` has
    already refused an as-of in the future, so ledger time really has
    reached `at`. It is also the one operation a concurrent writer cannot
    slip past: its own compare-and-set is against the same single row, so it
    either matches nothing or fails at commit with an isolation conflict,
    and `Ingest.record` reports both as `ConcurrentWrite` for retry.

    Returns the mark in force afterwards. Writes nothing when the window is
    already closed, which is every decision about the past.
    """
    at = dt(at)
    mark = Ingest(store).high_water()
    if mark is not None and instant(mark) >= instant(at):
        return mark
    if mark is None:
        advance = (f'match not {{ $x isa ledger,'
                   f' has ledger-id "{Ingest.LEDGER}"; }};'
                   f' insert $l isa ledger,'
                   f' has ledger-id "{Ingest.LEDGER}",'
                   f" has high-water {at};")
    else:
        advance = (f'match $l isa ledger, has ledger-id "{Ingest.LEDGER}",'
                   f" has high-water $h; $h == {mark};"
                   f" update $l has high-water {at};")
    try:
        store.write([advance], must_affect=True)
    except ConcurrentWrite:
        raise                       # commit-time conflict, already named
    except WriteMatchedNothing:
        # The compare-and-set lost its race: another writer moved the mark
        # between the read above and this write. That is retryable, and
        # reporting it as "a query matched nothing" sends the caller looking
        # at their data instead — the same confusion `retract` had, in the
        # code that fixed it.
        raise ConcurrentWrite(
            "the ledger moved while the as-of window was being closed: "
            "another writer recorded a fact concurrently. Retry."
        ) from None
    return at


def as_of(var: str, t: str) -> str:
    """A TypeQL fragment: `var` recorded by `t`, not retracted by `t`.

    Written once, here, because every domain's export needs it and a domain
    that writes its own risks getting the retraction half subtly wrong — the
    failure mode is a corrected fact that silently keeps deciding cases.
    """
    tag = var.lstrip("$")
    stamp = dt(t)
    return (f"{var} has recorded-at $ra_{tag}; $ra_{tag} <= {stamp}; "
            f"not {{ {var} has retracted-at $rx_{tag}; $rx_{tag} <= {stamp}; }};")


class Store:
    """A database holding the core schema plus one domain's."""

    def __init__(self, database: str, config: StoreConfig | None = None, *,
                 scratch: bool = False) -> None:
        """`scratch=True` drops the database when the Store is closed.

        A run that creates a throwaway database and deletes it on the last
        line leaks one every time it is interrupted — killed, or stopped by
        a dropped connection. Seventeen accumulated on the development
        server before anyone looked. Dropping it from `__exit__` instead
        means an exception, a Ctrl-C or a lost connection all still clean
        up, because `with` unwinds either way.
        """
        from typedb.driver import Credentials, TypeDB

        self.scratch = scratch
        self.database = ident(database)
        self.config = config or StoreConfig.from_env()
        credentials = Credentials(self.config.username, self.config.password)

        last: Exception | None = None
        for candidate in self.config.candidates():
            try:
                self.driver = TypeDB.driver(
                    candidate, credentials, self._options())
                self.address = candidate
                return
            except Exception as exc:
                last = exc
        raise ConnectionError(
            f"Could not reach TypeDB. Tried: "
            f"{', '.join(self.config.candidates())}. Last error: {last}")

    def _options(self) -> Any:
        """DriverOptions across two incompatible driver generations.

        The constructor changed between 3.8 and 3.13, and the driver has to
        match the *server*, so both are supported. Detection is by capability
        rather than by version string.
        """
        from typedb.driver import DriverOptions

        try:
            from typedb.driver import DriverTlsConfig
        except ImportError:                                # 3.8-era driver
            kwargs: dict[str, Any] = {"is_tls_enabled": self.config.tls}
            if self.config.tls_root_ca:
                kwargs["tls_root_ca_path"] = self.config.tls_root_ca
            return DriverOptions(**kwargs)

        if not self.config.tls:
            tls = DriverTlsConfig.disabled()
        elif self.config.tls_root_ca:
            tls = DriverTlsConfig.enabled_with_root_ca(self.config.tls_root_ca)
        else:
            tls = DriverTlsConfig.enabled_with_native_root_ca()
        return DriverOptions(tls)

    # ── schema and data ─────────────────────────────────────────────
    def reset(self, *schema_paths: pathlib.Path) -> None:
        """A fresh database: the core schema first, then the domain's."""
        from typedb.driver import TransactionType

        if self.driver.databases.contains(self.database):
            self.driver.databases.get(self.database).delete()
        self.driver.databases.create(self.database)
        self.write(CORE_SCHEMA.read_text(), TransactionType.SCHEMA)
        for path in schema_paths:
            self.write(pathlib.Path(path).read_text(), TransactionType.SCHEMA)

    def write(self, queries: str | list[str], kind: Any = None, *,
              must_affect: bool = False) -> None:
        """Run queries in ONE transaction, so a partial write cannot commit.

        With `must_affect`, a match-insert whose match found nothing aborts
        the whole transaction. Otherwise it writes nothing and reports
        success, and the caller goes on believing an edge exists — which is
        how a decision ends up with no reliance edges and looks unaffected by
        every correction thereafter.
        """
        from typedb.driver import TransactionType

        kind = TransactionType.WRITE if kind is None else kind
        batch = [queries] if isinstance(queries, str) else list(queries)
        with self.driver.transaction(self.database, kind) as tx:
            for index, query in enumerate(batch):
                if not query.strip():
                    continue
                answer = tx.query(query).resolve()
                if (must_affect and answer.is_concept_rows()
                        and not any(True for _ in answer.as_concept_rows())):
                    tx.rollback()
                    # the index is the position in the batch as the caller
                    # passed it, so a wrapper can tell its own queries from
                    # the caller's without parsing this message
                    raise WriteMatchedNothing(index, query)
            try:
                tx.commit()
            except Exception as exc:                      # noqa: BLE001
                # Overlapping writers both match their compare-and-set; the
                # engine stops the second at COMMIT with an isolation
                # conflict. That is the same failure as a lost CAS and must
                # read the same way, or retry logic misses it entirely.
                if "STC2" in str(exc) or "isolation conflict" in str(exc):
                    raise ConcurrentWrite(
                        "another writer committed a conflicting change: "
                        "retry this write"
                    ) from None
                raise

    def read(self):
        """A read transaction, so a whole export sees one consistent state."""
        from typedb.driver import TransactionType

        return self.driver.transaction(self.database, TransactionType.READ)

    def rows(self, query: str, tx: Any = None) -> list[dict[str, Any]]:
        if tx is not None:
            return self._rows(tx, query)
        with self.read() as own:
            return self._rows(own, query)

    @staticmethod
    def _rows(tx: Any, query: str) -> list[dict[str, Any]]:
        answer = tx.query(query).resolve()
        out = []
        for row in answer.as_concept_rows():
            record = {}
            for column in row.column_names():
                value = row.get(column)
                if value is None:
                    record[column] = None
                    continue
                native = value.try_get_value()
                # An integer stays an integer. Stringifying it turned every
                # numeric attribute into text on the way out of the store,
                # so a rule comparing a threshold had nothing numeric to
                # compare — and the Lean literal writer had to be handed a
                # number it could not get. Everything else keeps its string
                # form, which is what the rest of the system reads
                # (datetimes are sliced, keys are interpolated).
                if native is None:
                    # An entity or relation has no value, and `str(native)`
                    # made that the string "None" — indistinguishable from
                    # an attribute whose value is literally "None", and it
                    # would have reached a Lean literal as one. It stays
                    # `None`, which no attribute value can be.
                    #
                    # NOT an error: `Store.require` deliberately selects a
                    # concept (`select $x`) and only counts rows. Raising
                    # here broke every subject check and so every live
                    # stage — I applied the finding without looking for the
                    # consumer it said did not exist.
                    record[column] = None
                    continue
                record[column] = (
                    native if isinstance(native, int)
                    and not isinstance(native, bool) else str(native))
            out.append(record)
        return out

    def require(self, tx: Any, pattern: str, what: str) -> None:
        """Refuse to proceed when a pattern that must match, does not.

        Used for the subject of a decision: an export that silently returns
        nothing for an unknown subject hands the rule a vacuous case.
        """
        if not self._rows(tx, f"match {pattern} select $x;"):
            raise UnknownSubject(
                f"{what}: refusing to treat an unknown subject as an empty "
                f"(and therefore decidable) case")

    def lookup(self, tx: Any, base: str, attrs: str, select: str,
               probe: str) -> list[dict[str, Any]]:
        """A lookup that proves it dropped nothing.

        Runs the query twice — with the exported attributes, and selecting
        only `probe` — and refuses if the counts differ. A fact missing a
        required attribute then fails the export instead of disappearing
        from it.
        """
        # Compared by IDENTITY, not by count. Counting let the two faults
        # cancel: one fact missing a required attribute (dropped from
        # `full`) plus one whose attribute pattern multiplied into two rows
        # gives equal totals, and both faults passed silently. Every fact
        # owns `fact-id @key`, so the two sides are compared as multisets of
        # fact ids and each fault is named separately even when both are
        # present.
        # A plain identifier: TypeQL rejects a leading underscore
        # (`$__probe_fid` is not an identifier_var), and the name has to not
        # collide with the ones domains bind.
        tag = "$probe_fid_"
        full_rows = self._rows(
            tx, f"match {base} {attrs} {probe} has fact-id {tag};"
                f" select {select}, {tag};")
        bare_rows = self._rows(
            tx, f"match {base} {probe} has fact-id {tag}; select {tag};")
        key = tag[1:]
        seen = collections.Counter(r[key] for r in full_rows)
        want = collections.Counter(r[key] for r in bare_rows)
        dropped = sorted((want - seen).elements())
        extra = sorted((seen - want).elements())
        if dropped:
            raise SnapshotIncomplete(
                f"export dropped {len(dropped)} fact(s) lacking required "
                f"attributes in: {base[:80]}… — {dropped[:5]}")
        if extra:
            # More rows WITH the attributes than facts means the attribute
            # pattern multiplied rows, so a fact would appear in the
            # snapshot more than once.
            raise SnapshotIncomplete(
                f"the attribute pattern multiplied rows in: {base[:80]}… "
                f"— {extra[:5]} would appear in the snapshot more than once")
        return [{k: v for k, v in row.items() if k != key}
                for row in full_rows]

    def close(self) -> None:
        self.driver.close()

    def __enter__(self) -> Store:
        return self

    def __exit__(self, *_: object) -> None:
        # drop first, then close: the drop needs the connection. Both are
        # best-effort, because a cleanup failure must not mask whatever the
        # caller was actually doing — including the exception that brought
        # us here.
        if getattr(self, "scratch", False):
            try:
                if self.driver.databases.contains(self.database):
                    self.driver.databases.get(self.database).delete()
            except Exception:                                 # noqa: BLE001
                pass
        self.close()


class Ingest:
    """The only write path for facts: stamps ledger time, refuses backdating.

    A domain subclasses this and adds one method per fact type, each calling
    :meth:`now` for the timestamp and :meth:`fact` to write. Sources never
    supply a time, because a fact recorded before an existing one would alter
    a snapshot that has already been decided.
    """

    def __init__(self, store: Store, clock=None) -> None:
        self.store = store
        self._previous: str | None = None
        self.clock = clock or (
            lambda: datetime.datetime.now(datetime.timezone.utc)
            .strftime("%Y-%m-%dT%H:%M:%S"))

    LEDGER = "attest-ledger"

    def high_water(self) -> str | None:
        """The latest ledger time, read from one row.

        Two earlier versions were wrong about cost. The first pulled every
        `recorded-at` and `retracted-at` in the store back to Python and took
        the max; the second reduced server-side but still scanned every fact.
        Both were O(all facts) on every write, for one scalar.
        """
        rows = self.store.rows(
            f'match $l isa ledger, has ledger-id "{self.LEDGER}",'
            f" has high-water $h; select $h;")
        if rows:
            return _trim(rows[0]["h"])
        # No ledger row. Either the store is empty, or it predates the
        # ledger — and in the second case the first write would have no mark
        # to check against and could be backdated under every fact already
        # there. Fall back to the facts, once.
        existing = [
            row["m"] for query in (
                "match $f isa fact, has recorded-at $t; reduce $m = max($t);",
                "match $f isa fact, has retracted-at $t; reduce $m = max($t);")
            for row in self.store.rows(query) if row.get("m") is not None
        ]
        return max((_trim(s) for s in existing), default=None)

    def record(self, *queries: str) -> str:
        """Write facts and advance the ledger, in ONE transaction.

        `{stamp}` in any query is replaced with the ledger time, so a caller
        never has to supply one — which is the point: sources do not get to
        choose when a fact was recorded.

        The ledger move is a compare-and-set against the value this call
        read. A second writer that advanced it in between makes the `match`
        find nothing, and `must_affect` turns that into a rollback — so two
        concurrent writers cannot both pass the clock check and record facts
        out of order. Returns the ledger time the facts were stamped with.
        """
        stamp = self.now()
        previous = self._previous
        if previous is None:
            advance = (f'match not {{ $x isa ledger,'
                       f' has ledger-id "{self.LEDGER}"; }};'
                       f' insert $l isa ledger,'
                       f' has ledger-id "{self.LEDGER}",'
                       f" has high-water {stamp};")
        else:
            advance = (f'match $l isa ledger, has ledger-id "{self.LEDGER}",'
                       f" has high-water $h; $h == {previous};"
                       f" update $l has high-water {stamp};")
        filled = [q.replace("{stamp}", stamp) for q in queries]
        try:
            self.store.write([advance, *filled], must_affect=True)
        except ConcurrentWrite:
            raise                      # commit-time conflict, already named
        except WriteMatchedNothing as exc:
            # A query matched nothing. WHICH one matters: the ledger advance
            # losing its compare-and-set is a concurrency problem the caller
            # should retry; one of the caller's own queries matching nothing
            # is a statement about their data, and saying "the ledger moved"
            # would send them looking in the wrong place entirely.
            #
            # The advance is always first in the batch below, so the index
            # says which it was — no parsing of the message, and nothing to
            # break if either side's wording changes.
            if exc.index == 0:
                raise ConcurrentWrite(
                    "the ledger moved while this write was being prepared: "
                    "another writer recorded a fact concurrently. Retry."
                ) from None
            raise
        return stamp

    #: one microsecond, as a fraction of a second
    TICK = datetime.timedelta(microseconds=1)
    #: how far behind the mark a clock may be and still be treated as skew
    #: rather than as a wrong clock. Generous against real skew, tight
    #: enough that a backdate of hours is still refused.
    SKEW_TOLERANCE = datetime.timedelta(minutes=5)

    def now(self) -> str:
        """The next ledger time: strictly later than the current mark.

        Equal is not good enough. Timestamps were recorded to the second, so
        two writes inside one second both compared equal and both passed —
        and a decision taken "as of" that second between the two commits
        sees the first fact and not the second. The second then lands inside
        an already-decided snapshot and replay breaks. Measured: a
        compare-and-set of X against X matches and commits.
        """
        mark = self.high_water()
        self._previous = mark
        stamp = dt(self.clock())
        if mark is None:
            return stamp
        if instant(stamp) <= instant(mark):
            # Behind the mark. Two very different causes, and they need
            # different answers:
            #
            #   a clock a little behind the mark — ordinary skew, or a mark
            #   that a decision moved ahead by sealing its as-of window —
            #   is stepped past, exactly as a same-second collision already
            #   was. Refusing here made one machine's skew everyone's
            #   problem: a decider whose clock ran two minutes fast sealed
            #   the mark two minutes ahead, and every other writer, with a
            #   correct clock, was refused as "backdating" until real time
            #   caught up. Stepping past also protects replay better than
            #   refusing does — the fact lands AFTER the sealed window
            #   instead of not landing at all.
            #
            #   a clock far behind the mark is not skew. It is a broken
            #   clock or a deliberate backdate, and silently restamping it
            #   would hide that, so it is still refused.
            behind = instant(mark) - instant(stamp)
            if behind > self.SKEW_TOLERANCE:
                raise ValueError(
                    f"ledger time {stamp} is {behind} before high-water mark "
                    f"{mark}: backdating refused")
            stamp = self._after(mark)
        return stamp

    @classmethod
    def _after(cls, mark: str) -> str:
        """The smallest ledger time strictly greater than `mark`."""
        base = mark if "." in mark else mark + ".000000"
        moment = datetime.datetime.strptime(base[:26], "%Y-%m-%dT%H:%M:%S.%f")
        return (moment + cls.TICK).strftime("%Y-%m-%dT%H:%M:%S.%f")

    def retract(self, fact_id: str) -> str:
        """Correct a fact by appending a retraction. Nothing is deleted.

        `must_affect` matters here: the guard `not { $f has retracted-at $x; }`
        makes a second retraction match nothing, and without it the write
        would report success while doing nothing — so a caller correcting an
        already-corrected fact would believe it had.
        """
        try:
            return self.record(
                f'match $f isa fact, has fact-id "{ident(fact_id)}";'
                f' not {{ $f has retracted-at $x; }};'
                f' insert $f has retracted-at {{stamp}};')
        except ConcurrentWrite:
            # Discriminate on the TYPE, not on the message. Matching
            # "ledger moved" caught only the compare-and-set failure; the
            # commit-time conflict says "another writer committed a
            # conflicting change" and was reported to the caller as "already
            # retracted, or does not exist" — a concurrency problem dressed
            # as a statement about their data, sending them to look in the
            # wrong place. This is the same coupling to message text that
            # `WriteMatchedNothing.index` was introduced to remove.
            raise
        except WriteMatchedNothing:
            raise VerificationError(
                f"fact {fact_id!r} is already retracted, or does not exist"
            ) from None
