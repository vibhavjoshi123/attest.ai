"""The decision procedure, and the parts of it that must not vary by domain.

One case runs like this:

    1. export a snapshot, in one read transaction, and hash it
    2. ask the untrusted search for a witness
    3. if there is one, ask the kernel to accept it as a proof of the rule
    4. if there is not, or it was rejected, ask the kernel to *decide* the
       rule's negation
    5. if that fails too, ask the kernel to decide the rule positively
    6. if the kernel settled nothing, the verdict is ERROR and is never
       recorded

Steps 3-5 are why a wrong search is survivable. The search proposes; every
answer is re-checked; and when the two differ the kernel wins and the
disagreement is reported rather than resolved quietly. A rejected witness is
reported too — "the search found something and it was wrong" is a different
fact about the world from "the search found nothing".
"""

from __future__ import annotations

import datetime
import hashlib
import json
import os
import pathlib
import uuid
import warnings
from dataclasses import dataclass, field
from typing import Any

from . import rulec, typebridge
from .domain import Domain, Snapshot
from .kernel import Check, Kernel, case_source
from .store import (UnknownSubject, VerificationError, dt, ident, instant,
                    seal_window, _trim)

def verdicts(rule) -> tuple[str, str]:
    """What to call the two outcomes.

    Named after the rule's own conclusion — `C` and `not C` — rather than a
    word the domain uses for the opposite case. The core cannot know what a
    given conclusion's opposite is called, and inventing the word would put
    a claim in the certificate that nothing proved.
    """
    return rule["conclusion"], f"not {rule['conclusion']}"


#: one sha-256 helper, defined in `typebridge`; there were three
sha256 = typebridge.sha


def hash_json(value: Any) -> str:
    return sha256(json.dumps(value, sort_keys=True, default=str))


#: one escaper for TypeQL string literals, defined in `typebridge`
tql_str = typebridge.tql_str


def lean_snapshot(snapshot: Snapshot, model, rule) -> str:
    """The snapshot as a Lean value of the GENERATED types.

    Generic: the element type of each collection comes from the rule, and the
    literal from the schema model, so provenance travels with every row and
    no domain writes a rendering.
    """
    missing = [c["name"] for c in rule["collections"]
               if c["name"] not in snapshot.data]
    if missing:
        # `.get(name, [])` would hand the kernel an empty list, and an empty
        # collection is not a neutral value: it refutes every `some` over it
        # and satisfies every `none of`. The rule would be decided — in the
        # reassuring direction — on data the export never looked for. This
        # bites when a rule family shares one export and a later rule
        # declares a collection the export was written before.
        raise VerificationError(
            f"the snapshot has no {', '.join(missing)}, which rule "
            f"{rule['id']} looks at: the export and the rule disagree about "
            f"what one case consists of")
    fields = []
    for collection in rule["collections"]:
        rows = snapshot.data.get(collection["name"], [])
        items = ",\n    ".join(
            typebridge.lean_literal(model, collection["type"], row)
            for row in rows)
        fields.append(f"{collection['name']} := [\n    {items}]")
    if rulec.scoped(rule):
        fields.append(f"subject := {typebridge.lean_str(snapshot.subject)}")
    given = dict(snapshot.params)
    for p in rule.get("params", []):
        if p["name"] not in given:
            raise VerificationError(
                f"rule {rule['id']} takes parameter {p['name']!r} and the "
                f"snapshot does not carry it")
        fields.append(f"{typebridge.camel(p['name'])} := "
                      f"{typebridge.lean_str(given[p['name']])}")
    if rulec.uses_as_of(rule):
        fields.append(f"asOfDay := {as_of_day(snapshot.as_of)}")
    return "def snap : Snapshot :=\n  { " + ",\n    ".join(fields) + " }\n"


@dataclass(frozen=True)
class CaseFile:
    """Everything that goes into one case file except the theorem itself.

    `decide` writes case files and `recheck` regenerates them to compare
    byte for byte. They used to assemble the parts separately — namespace,
    imports, opens, the snapshot definition and the `Iff.rfl` binding line —
    each with its own copy of the strings. Two copies of what must be one
    output is how a decision stops rechecking: change the binding line in
    `decide` and every proof it stores afterwards fails its own replay, or
    change it in `recheck` and every proof stored before does. Both now build
    the case from here, so there is one definition of what a case file is.
    """

    namespace: str
    imports: tuple[str, ...]
    opens: tuple[str, ...]
    #: `def snap …` followed by the binding line
    defs: str
    #: the rule's conclusion applied to this snapshot, and its negation
    positive: str
    negative: str

    def source(self, name: str, statement: str, proof: str) -> str:
        """The exact file for one theorem about this case."""
        return case_source(self.namespace, self.imports, self.opens,
                           self.defs, name, statement, proof)

    def check(self, kernel: Kernel, name: str, statement: str,
              proof: str) -> Check:
        return kernel.check(self.namespace, self.imports, self.opens,
                            self.defs, name, statement, proof)


def case_file(snapshot: Snapshot, model, rule, lean) -> CaseFile:
    """Build the case for `snapshot` under `rule`, in Lean package `lean`.

    The binding line is what ties the statement to the rule: `theorem holds
    : True := trivial` is accepted by a kernel check that only sees an opaque
    string, and this line makes the file assert that the proposition being
    proved IS the compiled rule's conclusion applied to this snapshot. If a
    local definition shadows the conclusion, or its name does not resolve,
    `Iff.rfl` fails to elaborate and the whole case is rejected.
    """
    conclusion = rule["conclusion"]
    rule_module = rulec.module(rule, lean.rules_namespace)
    positive = f"{conclusion} snap"
    binding = (f"example : ({positive}) ↔ "
               f"({rule_module}.{conclusion} snap) := Iff.rfl\n")
    return CaseFile(
        namespace=f"Case_{snapshot.sha256[:12]}",
        imports=(rule_module, *lean.theorem_modules),
        opens=(lean.schema_namespace, rule_module),
        defs=lean_snapshot(snapshot, model, rule) + binding,
        positive=positive, negative=f"¬ ({positive})")


def as_of_day(as_of: str) -> int:
    """The decision's instant as whole days since 1970-01-01, UTC.

    One definition, used for both the Lean snapshot and the argument handed
    to the TypeQL search, so "six months" cannot mean two different windows
    in the authority and in the thing that checks it. Truncating to a day is
    what makes a rule like "within six months" replayable: a decision re-run
    later in the same day reaches the same verdict.
    """
    stamp = dt(as_of).strip()
    date = stamp.split("T")[0]
    year, month, day = (int(part) for part in date.split("-"))
    return (datetime.date(year, month, day) - datetime.date(1970, 1, 1)).days


def search(store, rule, subject: str, subject_type: str, subject_key: str,
           as_of: str, params=None, model=None) -> list[list[str]]:
    """Call the TypeQL function COMPILED from the rule.

    Returns witnesses as lists of fact-ids, one per `some` in the rule, in
    rule order — which is exactly what the generic proof builder consumes.
    """
    function, _closure = rulec.fn_names(rule)
    variables = [f"$w{i}" for i, _ in enumerate(
        s for s in rule["steps"] if s["kind"] == "some")]
    # a rule that mentions `as-of-day` compiled to a function taking it, and
    # the value is the one the Lean snapshot carries, computed once
    extra, arguments = "", "$s, "
    given = dict(params or {})
    for i, p in enumerate(rule.get("params", [])):
        key = typebridge.key_attr(model, p["type"]) if model else None
        if key is None:
            raise VerificationError(
                f"parameter {p['name']!r}: {p['type']} needs exactly one "
                f"@key for the search to bind it")
        extra += (f' $a{i} isa {ident(p["type"])},'
                  f' has {ident(key)} "{ident(given[p["name"]])}";')
        arguments += f"$a{i}, "
    arguments += "$t"
    if rulec.uses_as_of(rule):
        # `+=`, not `=`. Assigning here discarded every parameter binding
        # built in the loop above, so the generated query called the
        # function with `$a0` never bound: any rule with both parameters and
        # a time window could not run at all.
        extra += f" let $d = {as_of_day(as_of)};"
        arguments += ", $d"
    rows = store.rows(
        f'match $s isa {ident(subject_type)},'
        f' has {ident(subject_key)} "{ident(subject)}";'
        f' let $t = {dt(as_of)};{extra}'
        f' let {", ".join(variables)} in {function}({arguments});'
        f' select {", ".join(variables)};')
    return [[row[v[1:]] for v in variables] for row in rows]


def _row_key(row):
    """A total order on snapshot rows, independent of how the store
    returned them. Facts have a unique `fact-id`, so that alone orders
    them; anything without one falls back to its canonical JSON."""
    if isinstance(row, dict) and row.get("fact-id") is not None:
        return (0, str(row["fact-id"]), "")
    return (1, "", json.dumps(row, sort_keys=True, default=str))


def make_snapshot(subject: str, as_of: str, data: dict[str, Any],
                  fact_ids=(), scope=(), assumptions=(),
                  params=None) -> Snapshot:
    """Build a snapshot with its canonical hash.

    Domains call this rather than hashing themselves, so two domains cannot
    disagree about what a snapshot hash is.

    A fact-id appearing twice is refused. The store guarantees uniqueness
    (`fact-id @key`) but the Lean types cannot — nothing stops a
    `List Observation` holding one id twice — and the exclusivity proofs for
    a rule family rest on fact-ids identifying a record. Supply a snapshot
    that breaks it and two branches of a binary gate both hold, each with a
    valid kernel proof. So the invariant is enforced where the snapshot is
    built, which is the one place that can see every row at once.
    """
    seen: dict[str, str] = {}
    for name, rows in data.items():
        if not isinstance(rows, list):
            continue                       # not a collection of rows
        for row in rows:
            if not isinstance(row, dict):
                continue
            fid = row.get("fact-id")
            if fid is None:
                continue
            if fid in seen:
                raise VerificationError(
                    f"fact-id {fid!r} appears twice in this snapshot "
                    f"({seen[fid]} and {name}): the proofs that two branches "
                    f"cannot both hold assume a fact-id identifies one record")
            seen[fid] = name
    # Canonical row order. `hash_json` sorts KEYS but not lists, and
    # `store.rows` makes no ordering promise, so the same facts in two
    # orders hashed to two different snapshots — and a stored decision
    # could then fail to reproduce its own `snapshot-hash`. Every domain
    # happens to sort its rows today; relying on each one remembering is
    # how this comes back. `relied_facts` walks these lists too, so its
    # answer — which becomes the certificate's `relied_on` and the stored
    # `reliance` edges — moved with the order as well.
    #
    # This is the same defect as witnesses hashing in search order, which
    # `Certificate.__post_init__` fixes; that fix was applied to witnesses
    # alone.
    data = {name: (sorted(rows, key=_row_key) if isinstance(rows, list)
                   else rows)
            for name, rows in data.items()}
    body = {"subject": subject, "as_of": as_of, "data": data}
    pairs = tuple(sorted((str(k), str(v)) for k, v in (params or {}).items()))
    if pairs:
        # only when present, so every snapshot taken before parameters
        # existed keeps the hash it was recorded with
        body["params"] = dict(pairs)
    return Snapshot(subject=subject, as_of=as_of, data=data,
                    sha256=hash_json(body), fact_ids=tuple(fact_ids),
                    scope=tuple(scope), assumptions=tuple(assumptions),
                    params=pairs)


@dataclass
class Certificate:
    verdict: str
    rule: str
    snapshot: Snapshot
    #: every witness the search returned, each a list of fact-ids in rule order
    witnesses: list[list[str]]
    witness_accepted: bool
    #: hash of the rule's STRUCTURE, names and prose dropped — so a later
    #: edit can be classified as the same obligation or a different one
    rule_shape: str
    #: which of the three attempts settled it: witness, negation, evaluation
    decided_by: str
    differential: str
    relied_on: list[str]
    kernel_version: str
    library_sha256: dict[str, str]
    schema_sha256: str
    accepted: list[dict[str, Any]]
    rejected: list[dict[str, Any]]
    #: artifact ids the proof was checked against
    artifacts: dict[str, str] = field(default_factory=dict)
    #: the accepted check in full, including its Lean source, for storage
    proof: dict[str, Any] | None = None
    sha256: str = ""

    def __post_init__(self) -> None:
        # TypeDB functions have bag semantics and no guaranteed order, so the
        # same decision over the same facts came back with its witnesses in a
        # different order between runs — and `witnesses` is hashed into
        # `certificate_sha256`. The certificate for one decision therefore
        # had no stable identity, which is most of what a certificate is for.
        # `decide` already sorted when CHOOSING a witness; this makes the
        # recorded form canonical too, on every construction path.
        self.witnesses = sorted(list(w) for w in self.witnesses)

    @property
    def settled(self) -> bool:
        return self.verdict != "ERROR"

    def as_dict(self) -> dict[str, Any]:
        body = {
            "verdict": self.verdict, "rule": self.rule,
            "snapshot": {"subject": self.snapshot.subject,
                         "as_of": self.snapshot.as_of,
                         "sha256": self.snapshot.sha256,
                         "scope": list(self.snapshot.scope),
                         "assumptions": list(self.snapshot.assumptions),
                         "data": self.snapshot.data,
                         **({"params": dict(self.snapshot.params)}
                            if self.snapshot.params else {})},
            "witnesses": self.witnesses,
            "witness_accepted": self.witness_accepted,
            # Both of these are STORED beside `certificate-hash` and both
            # are relied upon: `decisions_after_rule_change` makes its
            # same-obligation call entirely from `rule-shape`. Leaving them
            # out of the hash meant either could be altered afterwards and
            # the hash would still check. `fact_ids` likewise: it is what
            # `reliance` is written from for a negation verdict.
            "rule_shape": self.rule_shape,
            "decided_by": self.decided_by,
            "fact_ids": list(self.snapshot.fact_ids),
            "differential": self.differential, "relied_on": self.relied_on,
            "kernel": self.kernel_version,
            "library_sha256": self.library_sha256,
            "schema_sha256": self.schema_sha256,
            "artifacts": self.artifacts,
            "accepted": self.accepted, "rejected": self.rejected,
        }
        body["certificate_sha256"] = hash_json(body)
        return body


def sources_of(domain: Domain) -> list[tuple[str, str, str]]:
    """Everything whose exact text a decision is checked against.

    The generated types, the compiled rule, any hand-written theorems, and
    the rule source itself. Each is published as an artifact and cited, so a
    decision names the library it was judged by rather than implying it.
    """
    rule = rulec.load(domain.rule_path)
    module = rulec.module(rule, domain.lean.rules_namespace)
    out = [
        (domain.lean.schema_namespace, "schema-types",
         str(domain.lean.schema_path)),
        (module, "rule-library", str(rulec.lean_path(
            rule, domain.lean.directory, domain.lean.rules_namespace))),
        (f"{rule['id']}.rule", "rule-source", str(domain.rule_path)),
    ]
    out += [(m, "theorems", str(domain.lean.module_path(m)))
            for m in domain.lean.theorem_modules]
    return out


def _unsettled(rule, snapshot, found, attempts, kernel, domain, store,
               differential: str) -> Certificate:
    """A certificate with no verdict. `record` refuses it."""
    certificate = Certificate(
        verdict="ERROR", rule=f"{rule['id']} {rule['version']}",
        snapshot=snapshot, witnesses=[list(w) for w in found],
        witness_accepted=False, rule_shape=rulec.shape_sha(rule),
        decided_by="none", differential=differential, relied_on=[],
        kernel_version=kernel.version(),
        library_sha256={name: typebridge.sha(open(path).read())
                        for name, _kind, path in sources_of(domain)},
        schema_sha256=typebridge.sha(
            store.driver.databases.get(store.database).schema()),
        accepted=[], rejected=[a.as_dict() for a in attempts], proof=None)
    certificate.sha256 = certificate.as_dict()["certificate_sha256"]
    return certificate


def _differential(verdict, holds, found, witness_accepted, witness_check,
                  attempts) -> str:
    """How the search and the kernel compare on one decision.

    Pure, so each case can be tested without a store or a kernel.
    """
    # Only attempts that RAN say anything about the proof. A timeout used to
    # read exactly like a rejection, so a witness the kernel never finished
    # checking was reported as one it had rejected: with `C` then proved by
    # evaluation, the search and the kernel agreed on the verdict and the
    # certificate still said DISAGREE — which `record` refuses.
    unfinished = [a for a in attempts if not a.ran]
    if verdict == "ERROR":
        differential = (
            "n/a: no verdict; the kernel did not finish "
            f"({unfinished[0].reason}) — retrying may settle it"
            # any attempt that did not finish might settle it on a retry
            if unfinished
            else "n/a: no verdict; the kernel settled neither the rule nor "
                 "its negation")
    elif found and not witness_accepted and witness_check is not None \
            and not witness_check.ran and verdict == holds:
        differential = (f"agree: the kernel proved {verdict} by evaluation; "
                        f"the search's witness was not checked "
                        f"({witness_check.outcome}: {witness_check.reason})")
    elif found and not witness_accepted:
        # The kernel proved the negation, or rejected the witness and proved
        # the rule some other way: either way the search was wrong, and the
        # wording says how much of that was observed rather than assumed.
        differential = (
            f"DISAGREE: the search's witness was rejected by the kernel; the "
            f"kernel proved {verdict}"
            if witness_check is None or witness_check.ran else
            f"DISAGREE: the search found a witness the kernel did not finish "
            f"checking ({witness_check.outcome}), and the kernel proved "
            f"{verdict}")
    elif not found and verdict == holds:
        differential = (f"DISAGREE: the search found nothing; the kernel "
                        f"proved {verdict}")
    else:
        differential = "agree"
    return differential


def decide(store, domain: Domain, subject: str, as_of: str, *,
           kernel: Kernel | None = None,
           suppress_search: bool = False,
           params: dict[str, str] | None = None) -> Certificate:
    """Decide one case. Returns the rule's two verdicts, or ERROR.

    Before anything else the rule is recompiled and both deployed forms are
    required to match it, and the Lean types are required to match the live
    schema. A decision taken against a drifted rule would be checked against
    something nobody reviewed.
    """
    kernel = kernel or Kernel(domain.lean.directory)
    # A decision "as of" a future date is not replayable: a fact written
    # afterwards falls inside the as-of window and changes the snapshot, so
    # the certificate stops reproducing its own hash.
    now = datetime.datetime.now(datetime.timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%S")
    # Compared as instants, like `seal_window` and `Ingest.now` do. As text
    # these agreed only because both sides happen to be trimmed to the
    # second: a sub-second as-of would have ordered by string prefix, where
    # `...00.1` sorts before `...00.10`.
    if instant(as_of) > instant(now):
        raise VerificationError(
            f"as-of {dt(as_of)} is in the future (now {now}): a fact written "
            f"later would change this snapshot, so the decision could not be "
            f"replayed")
    rule = rulec.load(domain.rule_path)
    model = rulec.check(store, rule, domain.lean.directory,
                        domain.lean.rules_namespace,
                        domain.lean.schema_namespace)
    artifacts = typebridge.check_sync(
        store, str(domain.lean.schema_path), sources_of(domain),
        domain.lean.schema_namespace)

    declared = [p["name"] for p in rule.get("params", [])]
    given = dict(params or {})
    if sorted(given) != sorted(declared):
        raise VerificationError(
            f"rule {rule['id']} takes parameters {declared}; got "
            f"{sorted(given)}")
    # Refusing a FUTURE as-of is not enough on its own. It leaves the whole
    # gap between the last recorded fact and the decision's date open: with
    # the ledger at the 1st and a decision as of the 10th, a writer whose
    # clock read the 3rd was accepted, and its fact landed inside a snapshot
    # that had already been certified. Closing the window makes the as-of
    # set frozen, which is what the certificate's hash claims.
    #
    # Sealed HERE, immediately before the read, and not at the top of this
    # function: the ledger is shared state, and a decision that is then
    # refused for drift, out-of-sync types or a bad parameter had already
    # moved it for everyone. Everything that can refuse this decision
    # without touching the snapshot has now run.
    # The subject is checked BEFORE the window is closed. Every export
    # refuses an unknown subject (`store.require`), but it does so part-way
    # through building the snapshot — after the seal — so a decision about a
    # subject that does not exist still moved shared ledger state.
    if not store.rows(f'match $s isa {ident(domain.subject_type)},'
                      f' has {ident(domain.subject_key)}'
                      f' "{ident(subject)}"; select $s;'):
        raise UnknownSubject(
            f"no {domain.subject_type} {subject!r}: refusing to treat an "
            f"unknown subject as an empty (and therefore decidable) case")
    seal_window(store, as_of)
    snapshot = (domain.snapshot(store, subject, as_of, params=given)
                if declared else domain.snapshot(store, subject, as_of))
    # Whether impact analysis could actually see a later addition to each
    # collection. `sync` can only check that an anchor EXISTS; here the
    # snapshot names the items the export records as covered, so an anchor
    # that binds a player the export never records shows up as the blind
    # spot it is.
    if getattr(domain, "scope_anchors", None) != ():
        inert = unanchored(model, domain, rule,
                           covered_types={t for t, _k, _v in snapshot.scope})
        if inert:
            warnings.warn(
                f"rule {rule['id']}: this decision records no covered item "
                f"an anchor on {', '.join(inert)} could join to, so a fact "
                f"added to {'it' if len(inert) == 1 else 'them'} later will "
                f"not flag this decision. Record the anchored entity in the "
                f"snapshot's scope, or declare `scope_anchors = ()`.",
                stacklevel=2)
    if dict(snapshot.params) != {k: str(v) for k, v in given.items()}:
        raise VerificationError(
            f"the export returned a snapshot for parameters "
            f"{dict(snapshot.params)}, not the {given} asked about")
    # one definition of the case file, shared with `recheck` (see CaseFile)
    case = case_file(snapshot, model, rule, domain.lean)
    namespace, positive, negative = case.namespace, case.positive, case.negative
    holds, fails = verdicts(rule)

    def attempt(name: str, statement: str, proof: str):
        return case.check(kernel, name, statement, proof)

    # With the search suppressed there is nothing to agree or disagree WITH,
    # and saying "agree" asserted a concurrence that was never tested.
    found = [] if suppress_search else search(
        store, rule, subject, domain.subject_type, domain.subject_key, as_of,
        params=given, model=model)
    attempts: list[Any] = []
    verdict = used = None
    witness_accepted = False
    # which attempt settled it, recorded with the verdict rather than left
    # implicit in the shape of `accepted`
    decided_by = "none"

    witness_check = None                # the attempt on the search's witness
    if found:
        witness = sorted(found)[0]           # deterministic across re-runs
        term = rulec.witness_proof(rule, model, snapshot.data, witness)
        if term is None:
            # The search found a conflict out of facts the export did not
            # produce. That is a statement about the EXPORT, not about the
            # subject: proceeding would prove the negation over a snapshot
            # already known to be missing something, and record it as a
            # verdict. This is the "missing data means safe" failure wearing
            # a different hat, so it terminates here.
            incomplete = Check(
                theorem=f"{namespace}.holds", name="holds",
                statement=positive, proof="", accepted=False, axioms=(),
                reason="snapshot incomplete: the search's witness names facts "
                       "the export did not produce",
                file="", source="", outcome="not-run")
            attempts.append(incomplete)
            return _unsettled(rule, snapshot, found, attempts, kernel,
                              domain, store,
                              "n/a: snapshot incomplete, no verdict attempted")
        else:
            result = witness_check = attempt("holds", positive, term)
            attempts.append(result)
            if result.accepted:
                verdict = holds
                used = rulec.relied_facts(
                    rule, model, snapshot.data, witness,
                    scopes={"subject": snapshot.subject, **given})
                witness_accepted = True
                decided_by = "witness"

    if verdict is None:                 # no usable witness: decide the negation
        result = attempt("fails", negative, "by decide")
        attempts.append(result)
        if result.accepted:
            verdict = fails
            used = list(snapshot.fact_ids)
            decided_by = "negation"

    if verdict is None:                 # the kernel may still settle it
        result = attempt("holds_by_decision", positive, "by decide")
        attempts.append(result)
        if result.accepted:
            verdict = holds
            used = list(snapshot.fact_ids)
            decided_by = "evaluation"

    if verdict is None:
        verdict = "ERROR"               # settled neither way; never recorded

    differential = _differential(verdict, holds, found, witness_accepted,
                                 witness_check, attempts)

    accepted = [a for a in attempts if a.accepted]
    certificate = Certificate(
        verdict=verdict, rule=f"{rule['id']} {rule['version']}",
        snapshot=snapshot, witnesses=[list(w) for w in found],
        witness_accepted=witness_accepted, rule_shape=rulec.shape_sha(rule),
        decided_by=decided_by, differential=differential,
        relied_on=used or [], kernel_version=kernel.version(),
        library_sha256={name: typebridge.sha(open(path).read())
                        for name, _kind, path in sources_of(domain)},
        schema_sha256=typebridge.sha(
            store.driver.databases.get(store.database).schema()),
        artifacts=artifacts,
        accepted=[a.as_dict() for a in accepted],
        rejected=[a.as_dict() for a in attempts if not a.accepted],
        proof=({**accepted[0].as_dict(), "source": accepted[0].source}
               if accepted else None),
    )
    certificate.sha256 = certificate.as_dict()["certificate_sha256"]
    return certificate


# ── write-back, in core types only ──────────────────────────────────
def record(store, certificate: Certificate, subject_type: str,
           subject_key: str, decided_at: str, *,
           allow_disagreement: bool = False) -> str:
    """Decision, proof, reliance and coverage in ONE transaction.

    NOT governance: `govern()` writes that, separately, and the two are not
    atomic. This docstring used to claim otherwise. A caller that records
    and never calls `govern` stores a decision citing no artifacts, which
    `recheck` then refuses forever — and nothing says so at write time.

    Uses only core types, so this works for any domain without knowing one of
    its type names. An unsettled verdict is refused rather than stored: a
    decision row that says ERROR is a decision nobody made.
    """
    rule = certificate.rule
    if not certificate.settled:
        raise VerificationError(
            f"refusing to record verdict {certificate.verdict!r}: "
            f"{[r.get('reason') for r in certificate.rejected]}")
    # A disagreement means the search and the kernel read the same facts
    # differently — usually because the trusted export missed something the
    # untrusted search saw. Storing the verdict anyway leaves the only trace
    # of the contradiction in a prose field.
    if certificate.differential.startswith("DISAGREE") and (
            not allow_disagreement):
        raise VerificationError(
            f"refusing to record a contradicted verdict: "
            f"{certificate.differential}. Pass allow_disagreement=True to "
            f"record it anyway, deliberately.")

    snapshot = certificate.snapshot
    decision_id = "dec-" + uuid.uuid4().hex[:16]
    queries = [
        f'match $s isa {ident(subject_type)},'
        f' has {ident(subject_key)} "{ident(snapshot.subject)}";'
        f' insert $d isa decision, links (subject: $s),'
        f' has decision-id "{decision_id}",'
        f' has verdict {tql_str(certificate.verdict)},'
        f' has snapshot-hash "{snapshot.sha256}",'
        f' has certificate-hash "{certificate.sha256}",'
        f' has rule-version {tql_str(rule)},'
        f' has rule-shape "{certificate.rule_shape}",'
        f' has decided-by {tql_str(certificate.decided_by)},'
        f' has as-of {dt(snapshot.as_of)},'
        f' has decided-at {dt(decided_at)}'
        + (f', has decision-inputs '
           f'{tql_str(json.dumps(dict(snapshot.params), sort_keys=True))}'
           if snapshot.params else '') + ';'
    ]
    if certificate.proof:
        proof = certificate.proof
        queries.append(
            f'match $d isa decision, has decision-id "{decision_id}";'
            f' insert $p isa proof,'
            f' has proof-id "prf-{uuid.uuid4().hex[:16]}",'
            f' has theorem-name {tql_str(proof["name"])},'
            f' has statement {tql_str(proof["statement"])},'
            f' has proof-term {tql_str(proof["proof"])},'
            f' has proof-source {tql_str(proof["source"])},'
            f' has axioms-used {tql_str(",".join(proof["axioms"]))},'
            f' has kernel-version {tql_str(certificate.kernel_version)};'
            f' proved-by (decision: $d, proof: $p);')
    queries += [
        f'match $d isa decision, has decision-id "{decision_id}";'
        f' $e isa fact, has fact-id "{ident(f)}";'
        f' insert reliance (decision: $d, evidence: $e);'
        for f in certificate.relied_on
    ]
    # `scope` is (type, key-attribute, value) triples. The type is named
    # because an attribute alone is ambiguous — `name` may be owned by a type
    # that does not play `coverage:item`, and inference then fails rather than
    # narrowing. The domain supplies it, exactly as it supplies the subject
    # type above; the core still never has one compiled in.
    queries += [
        f'match $d isa decision, has decision-id "{decision_id}";'
        f' $x isa {ident(type_name)}, has {ident(key_attr)} "{ident(value)}";'
        f' insert coverage (decision: $d, item: $x);'
        for type_name, key_attr, value in certificate.snapshot.scope
    ]
    # every match-insert here binds the decision, a fact or a covered
    # item; if any of them matches nothing the decision would be stored
    # with edges missing, so the whole transaction is aborted instead.
    store.write(queries, must_affect=True)
    return decision_id


def decisions_after_rule_change(store, rule) -> list[dict[str, Any]]:
    """Stored decisions classified against the rule as it stands NOW.

    Editing a rule used to orphan its whole history: every decision cited a
    `rule-version` that no longer matched, and nothing could tell a renamed
    variable from a changed threshold. Each decision now carries the rule's
    SHAPE as well, so the two cases separate:

      `same obligation`      the rule asks the same question. The decision
                             should still hold; re-check it to confirm, and
                             a failure is a real regression.
      `different obligation` the question itself changed. The old verdict is
                             not wrong, it answered something else, and a
                             re-check is not a comparison but a new
                             decision.

    This is Why3's distinction — exact hash for identity, shape for near
    identity — which is the thing that keeps a proof session useful across
    specification edits rather than throwing it away.
    """
    want_shape = rulec.shape_sha(rule)
    rule_id = rule["id"]
    out = []
    for row in store.rows(
            f"match $d isa decision, has decision-id $did,"
            f" has verdict $v, has rule-version $rv, has rule-shape $rs,"
            f" has decided-by $db, has as-of $t;"
            f" select $did, $v, $rv, $rs, $db, $t;"):
        if not row["rv"].startswith(rule_id + " "):
            continue
        same = row["rs"] == want_shape
        out.append({**row,
                    "same_obligation": same,
                    "why": ("the rule asks the same question; re-check to "
                            "confirm the verdict still holds")
                           if same else
                           ("the rule asks a different question; this "
                            "verdict answered the old one")})
    return sorted(out, key=lambda r: r["t"])


def _reject_module_collision(domain: Domain, rule) -> None:
    """Refuse a rule that would overwrite a different rule's Lean module.

    `rulec.segments` maps the whole id to the module path, so two rules can
    only collide here by having the same id — a family (`policy.open`,
    `policy.review`) compiles to one module each. The check stays because
    the failure it prevents is silent: the second rule overwrites the first,
    and the drift check then reports `Drift` on a rule nobody touched.
    """
    path = rulec.lean_path(rule, domain.lean.directory,
                           domain.lean.rules_namespace)
    if not os.path.exists(path):
        return
    existing = open(path).read()
    marker = f'def ruleId : String := "{rule["id"]} '
    if "def ruleId" in existing and marker not in existing:
        other = existing.split('def ruleId : String := "')[1].split('"')[0]
        raise rulec.RuleError(
            f"rule {rule['id']!r} compiles to the same module as {other!r}: "
            f"two rules cannot share an id")


def sync(store, domain: Domain):
    """Deploy the compiled search, then generate the Lean types, then compile
    the Lean rule. The order is not arbitrary.

    The generated types carry a hash of the whole schema — types *and*
    functions — so they must be written after the search functions are
    defined, or the hash is of a schema that no longer exists and
    :func:`decide` refuses every case. Getting this backwards fails closed,
    which is the right direction, but it fails on every case rather than
    obviously once.
    """
    rule = rulec.load(domain.rule_path)
    _reject_module_collision(domain, rule)

    # 1. the untrusted search, compiled from the rule
    model = typebridge.parse(
        store.driver.databases.get(store.database).type_schema())
    deployed = rulec.live_functions(
        store.driver.databases.get(store.database).schema())
    wanted = rulec.live_functions(rulec.compile_typeql(rule, model))
    missing = {n: s for n, s in wanted.items() if n not in deployed}
    if missing:
        from typedb.driver import TransactionType
        store.write("define\n" + "\n".join(missing.values()),
                    TransactionType.SCHEMA)

    # 2. the Lean types, hashing the schema now that it is complete
    model, _hash = typebridge.generate(
        store, str(domain.lean.schema_path), domain.lean.schema_namespace)

    # 3. the Lean rule, the authority
    path = rulec.lean_path(rule, domain.lean.directory,
                           domain.lean.rules_namespace)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as handle:
        handle.write(rulec.compile_lean(rule, model,
                                        domain.lean.rules_namespace,
                                        domain.lean.schema_namespace))

    # 4. say so now if impact analysis has a blind spot. A collection no
    # anchor covers is one where a fact ADDED later can never flag an
    # earlier decision, and nothing else would ever mention it. An explicit
    # `scope_anchors = ()` is the domain saying that absence is deliberate.
    if getattr(domain, "scope_anchors", None) != ():
        blind = unanchored(model, domain, rule)
        if blind:
            warnings.warn(
                f"rule {rule['id']}: no affected_decisions anchor covers "
                f"{', '.join(blind)}, so a fact added to "
                f"{'it' if len(blind) == 1 else 'them'} later will not flag "
                f"an earlier decision. Declare an anchor on the domain, or "
                f"`scope_anchors = ()` if that is deliberate.",
                stacklevel=2)
    return rule, model


def anchors(model, domain, rule=None) -> tuple[str, ...]:
    """The `affected_decisions` anchors for `domain`: its own, then the
    ones its rule implies (`rulec.scope_anchors`) that it did not write.

    `model` is the schema model (`typebridge.parse` of the live type schema)
    — the anchors depend on which fields are roles. Pass the result to
    `affected_decisions` in place of `domain.scope_anchors`.
    """
    rule = rule or rulec.load(domain.rule_path)
    own = tuple(getattr(domain, "scope_anchors", ()) or ())
    have = {rulec.anchor_key(a) for a in own} - {None}
    return own + tuple(a for a in rulec.scope_anchors(rule, model)
                       if rulec.anchor_key(a) not in have)


def usable_anchors(model, patterns, covered_types=None):
    """The (type, role) keys of the anchors that could actually fire.

    An anchor fires by joining its role's player to a `coverage` edge, so it
    is inert unless the domain's export records that player as a covered
    item. With `covered_types` left out this is just "the anchor parses",
    which is what made a type-counting check report coverage for an anchor
    that could never match.
    """
    keys = [k for k in map(rulec.anchor_key, patterns) if k]
    if covered_types is None:
        return keys

    def recorded(tname):
        """Is this type, or one it inherits from, recorded as covered? A
        domain may record a parent (`substance`) where the anchor binds a
        child (`drug`); the coverage edge is on the same instance either
        way."""
        seen = set()
        while tname and tname not in seen:
            if tname in covered_types:
                return True
            seen.add(tname)
            tname = model["types"].get(tname, {}).get("sub")
        return False

    return [k for k in keys
            if recorded(typebridge.role_player(model, k[0], k[1]))]


def unanchored(model, domain, rule=None, covered_types=None) -> list[str]:
    """Relation types the rule reads that no USABLE anchor is about.

    Without `covered_types` this proves only that an anchor exists, which
    is weaker than it sounds. An anchor fires by joining its role's player
    to a `coverage` edge, so it is inert unless the domain's export records
    that player as a covered item. A rule may read a relation through a
    role whose player the export never records — a reference edge joined
    on its far end, say — and then the anchor can never match, while a
    check counting anchors by type calls the collection covered.

    Pass `covered_types` — the entity types the export records in
    `Snapshot.scope` — and an anchor counts only if its role's player is
    among them. The returned list is then the collections where a fact
    added later really would go unflagged.
    """
    rule = rule or rulec.load(domain.rule_path)
    patterns = anchors(model, domain, rule)
    keys = usable_anchors(model, patterns, covered_types)
    covered = {k[0] for k in keys}
    # A hand-written pattern of some other shape still counts for the type
    # it names: its join is not ours to second-guess. Tested over ALL the
    # patterns naming that type, not just the first one found — `next(...)`
    # made the answer depend on the order the domain happened to list its
    # anchors in, so the same domain could read covered or uncovered after
    # a harmless reordering.
    covered |= {c["type"] for c in rule["collections"]
                if any(f"isa {c['type']}," in p
                       and rulec.anchor_key(p) is None
                       for p in patterns)}
    return sorted({c["type"] for c in rule["collections"]} - covered)


def publish(store, domain: Domain, recorded_at: str) -> dict[str, str]:
    """Store the domain's sources as artifacts, keyed by hash.

    A decision then points at the exact rule and library its proof was
    checked against, so the pair can be re-checked from the store alone.
    """
    return typebridge.publish(store, sources_of(domain), dt(recorded_at))


def govern(store, decision_id: str, artifacts: dict[str, str]) -> None:
    """Link a decision to the artifacts its proof was checked against.

    `artifacts` maps artifact id to kind — the KEYS are the ids. It used to
    be the other way round, which meant one artifact per kind survived and a
    second theorem module was dropped on the floor.
    """
    store.write([
        f'match $d isa decision, has decision-id "{ident(decision_id)}";'
        f' $a isa artifact, has artifact-id "{ident(artifact_id)}";'
        f' insert governance (decision: $d, artifact: $a);'
        for artifact_id in sorted(artifacts)
    ], must_affect=True)


# ── re-verification from the store alone ────────────────────────────
@dataclass
class Recheck:
    """What a stored decision was re-checked against, and whether it held."""

    decision_id: str
    verdict: str
    passed: bool
    reason: str | None
    #: artifact id -> kind. Keyed the other way round, by KIND, it kept one
    #: artifact per kind: a domain with two theorem modules cited only one,
    #: and its decisions could never be re-checked against the other.
    artifacts: dict[str, str]
    workspace: str | None = None
    #: did the snapshot re-export to the hash the decision cites?
    snapshot_matches: bool = False
    #: did the case file regenerate byte for byte from that snapshot?
    file_matches: bool = False
    #: the toolchain recorded on the proof, and the one that just ran it
    kernel_recorded: str | None = None
    kernel_now: str | None = None

    def as_dict(self) -> dict[str, Any]:
        return {"decision_id": self.decision_id, "verdict": self.verdict,
                "passed": self.passed, "reason": self.reason,
                # `workspace` is deliberately absent: it is a temp
                # directory that changes every run, and it was being
                # serialised into committed example output, where it showed
                # up as a diff on every single run.
                "artifacts": self.artifacts,
                "snapshot_matches": self.snapshot_matches,
                "file_matches": self.file_matches,
                "kernel_recorded": self.kernel_recorded,
                "kernel_now": self.kernel_now}


def recheck(store, decision_id: str, *, domain, lean_dir=None,
            root_module=None, workdir: str | None = None) -> Recheck:
    """Re-verify a stored decision using only what the store holds.

    Not the working tree. The point is to answer "was this decision sound?"
    a year later, when the repository has moved on — so the Lean workspace
    is rebuilt from the artifacts the decision cited, and the proof is
    re-checked against *those*.

    This used to stop short of its own specification. It rebuilt the
    artifacts and re-ran whatever file was stored, then made three text
    checks: that the theorem line was present, that a leading `¬` agreed
    with the stored verdict, and that `Case_<hash>` occurred *somewhere* in
    the text — a bare substring, satisfied by a comment. Nothing tied the
    file's `def snap` to the facts the decision claims to be about, and the
    `Iff.rfl` line that stops a locally shadowed conclusion was not required
    either. So anyone able to write to TypeDB could store a file about
    different facts, or about an easier proposition, and have it re-verify.

    Now the snapshot is re-exported as of the decision's own as-of (hence
    `domain`), its hash is compared with the one the decision cites, and the
    case file is regenerated from that snapshot and compared **byte for
    byte** with the stored one. Once the file is known to be the file the
    core would generate, the keyword denylist and the three text checks stop
    being load-bearing: they are kept as defence in depth, not as the
    argument.

    Each of these is a separate way to fail:
      the cited artifacts still hash to their recorded sha256;
      the snapshot re-exports to the cited hash;
      the case file regenerates byte for byte;
      the workspace built from the artifacts compiles;
      the kernel accepts the stored source in that workspace;
      the axioms report is for this theorem, and within the allow-list;
      the statement, the verdict's polarity and the snapshot namespace agree.
    """
    did = ident(decision_id)
    lean_dir = lean_dir if lean_dir is not None else domain.lean.directory
    root_module = root_module or domain.lean.root_module

    rows = store.rows(
        f'match $d isa decision, has decision-id "{did}", has verdict $v,'
        f" has snapshot-hash $s, has rule-version $r, has as-of $ao;"
        f" select $v, $s, $r, $ao;")
    if not rows:
        raise VerificationError(f"no decision {decision_id!r}")
    decision = rows[0]

    inputs = store.rows(
        f'match $d isa decision, has decision-id "{did}",'
        f" has decision-inputs $i; select $i;")
    params = json.loads(inputs[0]["i"]) if inputs else {}

    subjects = store.rows(
        f'match $d isa decision, has decision-id "{did}";'
        f" $d links (subject: $s);"
        f' $s isa {ident(domain.subject_type)},'
        f" has {ident(domain.subject_key)} $k; select $k;")
    if not subjects:
        return Recheck(did, decision["v"], False,
                       "the decision names no subject of type "
                       f"{domain.subject_type!r}", {})
    subject = subjects[0]["k"]

    proofs = store.rows(
        f'match $d isa decision, has decision-id "{did}";'
        f" proved-by (decision: $d, proof: $p);"
        f" $p has theorem-name $n, has statement $st, has proof-term $t,"
        f" has proof-source $src, has axioms-used $a, has kernel-version $kv;"
        f" select $n, $st, $t, $src, $a, $kv;")
    if not proofs:
        return Recheck(did, decision["v"], False,
                       "no proof is stored for this decision", {})
    proof = proofs[0]

    governing = store.rows(
        f'match $d isa decision, has decision-id "{did}";'
        f" governance (decision: $d, artifact: $a);"
        f" $a has artifact-id $aid, has artifact-kind $k,"
        f" has lean-source $src, has source-sha256 $h;"
        f" select $aid, $k, $src, $h;")
    if not governing:
        return Recheck(did, decision["v"], False,
                       "no artifacts are cited by this decision", {})

    artifacts: dict[str, str] = {}
    stored_rule_source = stored_rule_library = None
    stored_schema_types = None
    for row in governing:
        if sha256(row["src"]) != row["h"]:
            return Recheck(did, decision["v"], False,
                           f"artifact {row['aid']} does not match its "
                           f"recorded hash", artifacts)
        artifacts[row["aid"]] = row["k"]
        if row["k"] == "rule-source":
            stored_rule_source = row["src"]
        elif row["k"] == "rule-library":
            stored_rule_library = row["src"]
        elif row["k"] == "schema-types":
            stored_schema_types = row["src"]

    # ── §7.8 step 2: re-export, and confirm the hash ────────────────
    if stored_rule_source is None:
        return Recheck(did, decision["v"], False,
                       "no rule source is cited, so the case file cannot be "
                       "regenerated", artifacts)
    try:
        rule = rulec.parse(stored_rule_source)
    except Exception as exc:                                  # noqa: BLE001
        return Recheck(did, decision["v"], False,
                       f"the stored rule source does not parse: "
                       f"{str(exc)[:200]}", artifacts)
    # The as-of has to be the STRING the decision hashed, not merely the
    # same instant. TypeDB returns a datetime at nanosecond precision, so
    # the stored `2026-10-10T00:00:00` reads back as
    # `2026-10-10T00:00:00.000000000`; `as_of` is part of the snapshot hash,
    # so re-exporting with the padded form hashed differently and every
    # clean recheck reported the facts as changed when nothing had.
    as_of_stored = _trim(decision["ao"])
    try:
        snapshot = (domain.snapshot(store, subject, as_of_stored,
                                    params=params)
                    if rule.get("params") else
                    domain.snapshot(store, subject, as_of_stored))
    except Exception as exc:                                  # noqa: BLE001
        return Recheck(did, decision["v"], False,
                       f"the snapshot does not re-export: "
                       f"{type(exc).__name__}: {str(exc)[:200]}", artifacts)
    if snapshot.sha256 != decision["s"]:
        return Recheck(did, decision["v"], False,
                       f"the snapshot no longer re-exports to the hash this "
                       f"decision cites: {decision['s'][:12]} recorded, "
                       f"{snapshot.sha256[:12]} now", artifacts)

    # ── §7.8 step 3: regenerate the case file, byte for byte ────────
    # The model has to be the one this decision was taken against, or a
    # byte difference in the regenerated file gets blamed on tampering when
    # the real cause is a schema that moved. Rendered from the live schema
    # and then held to the stored artifact, so a drifted schema is reported
    # as itself.
    if stored_schema_types is not None:
        ok, model, why = typebridge.types_match(
            store, stored_schema_types, domain.lean.schema_namespace)
        if not ok:
            return Recheck(did, decision["v"], False,
                           f"{why}, so its case file cannot be regenerated "
                           f"faithfully", artifacts, snapshot_matches=True)
    else:
        model = typebridge.parse(
            store.driver.databases.get(store.database).type_schema())
    # The stored Lean rule is what the stored RULE TEXT compiles to. Nothing
    # checked this: the two were published as separate artifacts and each
    # was only held to its own hash, so a rule module that did not come from
    # its own `.rule` file re-verified.
    if stored_rule_library is not None:
        recompiled = rulec.compile_lean(rule, model,
                                        domain.lean.rules_namespace,
                                        domain.lean.schema_namespace)
        if recompiled != stored_rule_library:
            return Recheck(did, decision["v"], False,
                           "the stored Lean rule module is not what the "
                           "stored rule source compiles to", artifacts,
                           snapshot_matches=True)
    # the same builder `decide` used, so "regenerate" cannot drift from
    # "generate" (see CaseFile)
    try:
        case = case_file(snapshot, model, rule, domain.lean)
    except Exception as exc:                                  # noqa: BLE001
        return Recheck(did, decision["v"], False,
                       f"the snapshot does not render as Lean: "
                       f"{type(exc).__name__}: {str(exc)[:200]}", artifacts)
    namespace = case.namespace
    regenerated = case.source(proof["n"], proof["st"], proof["t"])
    if regenerated != proof["src"]:
        return Recheck(did, decision["v"], False,
                       "the stored case file is not what this snapshot and "
                       "this rule generate: it has been altered, or the "
                       "generator has changed", artifacts,
                       snapshot_matches=True)

    # ── §7.8 step 4: rebuild from the store, and re-run the kernel ──
    try:
        workspace = typebridge.materialize(
            store, sorted(artifacts), str(lean_dir), root_module, workdir)
    except Exception as exc:                                  # noqa: BLE001
        return Recheck(did, decision["v"], False,
                       f"artifacts do not rebuild: {str(exc)[-400:]}",
                       artifacts, snapshot_matches=True, file_matches=True)

    kernel = Kernel(pathlib.Path(workspace))
    # materialize already ran `lake build` here
    kernel._built_at = kernel._fingerprint()
    now = kernel.version()
    out = dict(artifacts=artifacts, workspace=workspace,
               snapshot_matches=True, file_matches=True,
               kernel_recorded=proof["kv"], kernel_now=now)
    path = pathlib.Path(workspace) / "Cases" / f"recheck_{did}.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(proof["src"])
    completed = kernel.check_source(proof["src"], path, proof["n"],
                                    qualified=f"{namespace}.{proof['n']}")

    if not completed.accepted:
        return Recheck(did, decision["v"], False,
                       f"the stored proof no longer checks: "
                       f"{completed.reason}", **out)
    stored_axioms = {a for a in proof["a"].split(",") if a}
    if set(completed.axioms) != stored_axioms:
        return Recheck(did, decision["v"], False,
                       f"axioms changed: stored {sorted(stored_axioms)}, "
                       f"now {list(completed.axioms)}", **out)
    # The stored statement must be the theorem the source actually states,
    # as a whole line. A substring test passed for any statement that
    # happened to occur anywhere in the text — and `C snap` occurs inside
    # `¬ (C snap)`, so the negation of a claim satisfied a test for the
    # claim.
    if f"theorem {proof['n']} : {proof['st']} :=" not in proof["src"]:
        return Recheck(did, decision["v"], False,
                       f"the stored source does not state "
                       f"{proof['st']!r} as {proof['n']!r}", **out)

    # Bind the proof to the VERDICT. Nothing did: the verdict was read from
    # the store and never compared with what was proved, so a decision whose
    # stored verdict had been flipped from `not C` to `C` re-verified
    # happily — the proof still checked, it just proved the opposite.
    # Checked against the rule's own two verdicts rather than the prefix
    # "not ", so a stored verdict that is neither of them is refused too
    # instead of counting as "not negated" and agreeing with a positive
    # proof.
    holds, fails = verdicts(rule)
    if decision["v"] not in (holds, fails):
        return Recheck(did, decision["v"], False,
                       f"the stored verdict {decision['v']!r} is neither "
                       f"{holds!r} nor {fails!r}", **out)
    negated = proof["st"].lstrip().startswith("¬")
    if negated != (decision["v"] == fails):
        return Recheck(did, decision["v"], False,
                       f"the stored proof proves {proof['st']!r}, but the "
                       f"stored verdict is {decision['v']!r}", **out)

    # Bind the proof to the SNAPSHOT this decision cites. Redundant now that
    # the whole file is compared, and kept as the cheap direct statement of
    # the property.
    if namespace not in proof["src"]:
        return Recheck(did, decision["v"], False,
                       f"the stored proof is not about the snapshot this "
                       f"decision cites ({namespace} absent)", **out)
    return Recheck(did, decision["v"], True, None, **out)


# ── impact analysis ─────────────────────────────────────────────────
_DECISION_TAIL = (
    '$d isa decision, has decision-id $did, has verdict $v,'
    ' has decided-at $t, has snapshot-hash $h;')
_DECISION_COLS = "$did, $v, $t, $h"


def _before(a: str, b: str) -> bool:
    """Whether instant `a` is strictly before `b`, at full precision.

    Parsed rather than compared as text: ISO-8601 strings with differing
    numbers of fractional digits do not order lexicographically (`.9` sorts
    after `.10`).
    """
    try:
        return (datetime.datetime.fromisoformat(a.replace(" ", "T"))
                < datetime.datetime.fromisoformat(b.replace(" ", "T")))
    except ValueError:                       # unparseable: fall back to text
        return a < b


def decisions_relying_on(store, fact_id: str) -> list[dict[str, Any]]:
    """Decisions that used this fact — the retraction half."""
    return store.rows(
        f'match $e isa fact, has fact-id "{ident(fact_id)}";'
        f' reliance (decision: $d, evidence: $e);'
        f' {_DECISION_TAIL} select {_DECISION_COLS};')


_NO_ANCHORS = object()


def affected_decisions(store, fact_id: str,
                       scope_anchors=_NO_ANCHORS) -> list[dict[str, Any]]:
    """Decisions a change to `fact_id` may invalidate.

    Two halves, and both are needed:

    * **retraction** — decisions that relied on the fact.
    * **addition** — decisions taken *before* the fact was recorded whose
      snapshot covered an item the fact is about. Without this, adding a fact
      silently leaves every earlier decision looking valid.

    `scope_anchors` are domain-supplied patterns binding `$d` through a
    `coverage` edge; the core cannot know which role of which relation makes
    a fact "about" a covered item.
    """
    if scope_anchors is _NO_ANCHORS:
        raise TypeError(
            "affected_decisions needs scope_anchors. Without them only the "
            "retraction half runs, and a fact added later silently leaves "
            "every earlier decision looking valid. Pass domain.scope_anchors, "
            "or () to say that absence is deliberate.")
    fid = ident(fact_id)
    hits: dict[str, dict[str, Any]] = {}
    for row in decisions_relying_on(store, fid):
        hits[row["did"]] = {**row, "why": "relied on it"}

    stamp = store.rows(
        f'match $e isa fact, has fact-id "{fid}", has recorded-at $r;'
        f' select $r;')
    recorded = stamp[0]["r"] if stamp else None
    if not recorded:
        return sorted(hits.values(), key=lambda r: r["t"])

    for anchor in scope_anchors:
        for row in store.rows(
                f'match {anchor.format(fid=fid)} {_DECISION_TAIL}'
                f' select {_DECISION_COLS};'):
            # At full precision. Both sides used to be truncated to the
            # second and compared with `<`, so a fact recorded a microsecond
            # AFTER a decision was not flagged as affecting it — and
            # `Ingest.now()` steps to microseconds for the express purpose
            # of keeping same-second events ordered. The truncation threw
            # away the only thing that distinguished them.
            if _before(row["t"], recorded) and row["did"] not in hits:
                hits[row["did"]] = {
                    **row, "why": "in scope when the fact was added"}
    return sorted(hits.values(), key=lambda r: r["t"])
