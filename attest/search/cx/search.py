"""The counterexample search: propose, screen, shrink, confirm.

The pipeline is cheapest-first, and each stage is thousands of times
dearer than the last:

    generators -> well_formed -> screen -> violated? -> shrink
               -> signature dedup -> confirm (kernel) -> fixture

`screen` reads the declaration over the reference evaluator's verdicts in
microseconds. `confirm` asks the Lean kernel, which takes seconds. So the
search looks at millions of worlds and confirms a handful, and a
counterexample is only reported when the kernel agreed about every verdict
the violation needs — with standard axioms and nothing else.

Shrinking happens before confirmation, not after: a violation on two rows
is a bug report a person can read, one on twelve rows is a puzzle, and
shrinking on the evaluator costs microseconds while confirming the big one
costs seconds.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Any, Callable, Iterator

from attest import rulec
from attest.props import PropertyDecl
from attest.search.cx import guide
from attest.search.cx.generators import (
    Candidate,
    future_dated,
    mutants,
    small_scope,
)
from attest.search.cx.props_eval import predicate
from attest.search.cx.world_set import (
    DUPLICATE,
    WorldSet,
    matches_when,
    same_reading,
)


@dataclass
class Violation:
    """A world on which a declared property does not hold."""

    decl_id: str
    kind: str
    world: dict
    before: dict | None
    verdicts: dict[str, bool]
    verdicts_after: dict[str, bool] | None
    signature: str
    origin: dict
    shrink_log: list[str] = field(default_factory=list)
    rank: int = 0
    #: filled by `confirm`
    kernel: dict[str, Any] = field(default_factory=dict)

    def as_dict(self) -> dict:
        return {
            "property": self.decl_id, "kind": self.kind,
            "signature": self.signature,
            "world": self.world, "before": self.before,
            "verdicts": self.verdicts, "verdicts_after": self.verdicts_after,
            "origin": self.origin, "shrink_log": self.shrink_log,
            "rank": self.rank, "kernel": self.kernel,
        }


def _needs_change(decl: PropertyDecl) -> bool:
    return decl.kind in ("stable-add", "stable-retract")


def screen(cand: Candidate, decl: PropertyDecl, rules: dict,
           model) -> tuple[bool, dict, dict | None]:
    """(violated, verdicts, verdicts_after) from the reference evaluator."""
    holds = predicate(decl)
    if _needs_change(decl):
        if cand.before is None:
            return False, {}, None
        before = cand.before.verdicts(rules, model)
        after = cand.ws.verdicts(rules, model)
        return (not holds(before, after)), before, after
    verdicts = cand.ws.verdicts(rules, model)
    return (not holds(verdicts)), verdicts, None


def _change_in_scope(cand: Candidate, decl: PropertyDecl) -> bool:
    """Is the change this candidate makes one the declaration is about?

    Two restrictions, and both matter. The change must be to a collection
    the declaration names, and the row it touches must satisfy `when`.
    Fixture's claim is about rows dated AFTER the decision; a row dated
    before is exactly the row a working rule is supposed to react to, so
    counting it as a violation reports every correct rule as broken.
    """
    if cand.before is None:
        return False
    for coll in (decl.collections or tuple(cand.ws.data)):
        was = {r.get("fact-id") for r in cand.before.data.get(coll, [])}
        now = cand.ws.data.get(coll, [])
        existing = cand.before.data.get(coll, [])
        for row in now:
            if row.get("fact-id") in was:
                continue
            if (decl.when or "").strip() == DUPLICATE:
                if any(same_reading(row, old) for old in existing):
                    return True
                continue
            if matches_when(row, decl.when, cand.ws.as_of_day):
                return True
        if decl.kind == "stable-retract":
            for row in now:
                if row.get("retracted-at") and matches_when(
                        row, decl.when, cand.ws.as_of_day):
                    return True
    return False


def shrink(cand: Candidate, decl: PropertyDecl, rules: dict,
           model) -> tuple[Candidate, list[str]]:
    """The smallest world, by row removal, that still violates.

    Greedy and on the evaluator only. A violation that needs four rows to
    state is usually a violation about two of them.
    """
    log: list[str] = []
    current = cand
    changed = True
    while changed:
        changed = False
        for coll, row in list(current.ws.rows()):
            fid = row.get("fact-id")
            smaller = current.ws.without(coll, fid)
            if not smaller.data.get(coll) and _needs_change(decl):
                continue
            trial = Candidate(
                ws=smaller, origin=current.origin,
                before=(current.before.without(coll, fid)
                        if current.before is not None else None))
            violated, _v, _a = screen(trial, decl, rules, model)
            if violated and not guide.well_formed(trial.ws, model, rules):
                current = trial
                log.append(f"dropped {coll}/{fid}")
                changed = True
                break
    return current, log


def signature(cand: Candidate, decl: PropertyDecl, rules: dict,
              model) -> str:
    """A stable name for *this kind* of violation.

    Two worlds that break the same property for the same reason get the
    same signature, so a search that finds one defect a thousand ways
    reports it once. Built from the property, the verdicts, and each row's
    shape — its collection and which atoms it satisfies — with values
    abstracted away, because `amount = 71` and `= 95` are the same
    defect.
    """
    violated, verdicts, after = screen(cand, decl, rules, model)
    shape = []
    for coll, row in sorted(cand.ws.rows(),
                            key=lambda cr: (cr[0], str(cr[1].get("fact-id")))):
        atoms = []
        for step in rulec.all_steps(
                next(iter(rules.values()))["steps"]):
            if step["kind"] != "require":
                continue
            lhs = step.get("lhs", "")
            attr = lhs.split(".", 1)[1] if "." in lhs else lhs
            if attr in row:
                atoms.append(f"{attr}{step.get('op')}")
        shape.append((coll, tuple(sorted(set(atoms))),
                      row.get("retracted-at") is not None))
    body = json.dumps(
        {"p": decl.id, "v": verdicts, "a": after, "s": shape},
        sort_keys=True, default=str)
    return hashlib.sha256(body.encode()).hexdigest()[:12]


def _readings(violation: Violation):
    """The (label, world, verdicts) pairs a violation actually rests on.

    A change property rests on TWO readings: the verdicts before the change
    and the verdicts after it. `Violation.world` is the world AFTER, and
    `Violation.verdicts` are the verdicts BEFORE, so confirming
    `violation.verdicts` against `violation.world` asks the kernel about a
    pairing that was never claimed — and the kernel says so. Measured on
    defects 2 and 3: `latest-low` came back refuted with "`decide` proved
    that the proposition", which is the compiled rule correctly disagreeing
    with a verdict from the other world.

    A violation is confirmed only when BOTH readings are, because the claim
    is that the change moved a verdict: either half alone is consistent with
    a rule that is perfectly stable.
    """
    if violation.verdicts_after is None:
        return [("", violation.world, violation.verdicts)]
    before = violation.before or violation.world
    return [("@before", {"data": before["data"],
                         "subject": before.get("subject",
                                               violation.world["subject"]),
                         "as_of_day": before.get("as_of_day",
                                                 violation.world["as_of_day"])},
             violation.verdicts),
            ("@after", violation.world, violation.verdicts_after)]


def confirm(violation: Violation, rules: dict, model, lean,
            kernel) -> dict[str, Any]:
    """Ask the kernel about every verdict the violation rests on.

    No new trusted statement is introduced: each verdict goes through
    `runner.case_file`, whose `Iff.rfl` binding line already ties the
    theorem to the compiled rule. A violation counts only when every
    needed verdict is proved, with standard axioms.
    """
    from attest import runner
    from attest.kernel import STANDARD_AXIOMS

    out: dict[str, Any] = {}
    # Every verdict the violation claims must be checked, or it is not
    # confirmed. `all()` over the checks that ran is True when none ran, so
    # a violation whose rule names matched nothing in `rules` used to come
    # back confirmed having asked the kernel nothing.
    unchecked = sorted(name for name in violation.verdicts
                       if name not in rules)
    if violation.verdicts_after is not None:
        unchecked += sorted(f"{name}@after"
                            for name in violation.verdicts_after
                            if name not in rules)
        # A change property claims a verdict MOVED, so each rule needs a
        # reading on both sides. A rule read on one side only is checked
        # against nothing it could have changed from.
        one_side = set(violation.verdicts) ^ set(violation.verdicts_after)
        unchecked += sorted(f"{name} (read on one side of the change only)"
                            for name in one_side if name in rules)
    if unchecked:
        # Already unconfirmable; asking the kernel about the rest would only
        # spend checks on a report whose answer is fixed.
        return {"_unchecked": unchecked, "_confirmed": False}
    for label, world, verdicts in _readings(violation):
        ws = WorldSet(world["data"], world["subject"], world["as_of_day"])
        for name, rule in rules.items():
            want = verdicts.get(name)
            if want is None:
                continue
            case = ws.case(rule, model)
            snapshot = runner.make_snapshot(
                ws.subject, _as_of(ws.as_of_day), case.data,
                fact_ids=tuple(sorted(r.get("fact-id")
                                      for _c, r in ws.rows())))
            cf = runner.case_file(snapshot, model, rule, lean)
            if want:
                witness = list(case.witnesses()[0])
                term = rulec.witness_proof(rule, model, case.data, witness)
                check = cf.check(kernel, "holds", cf.positive, term)
            else:
                check = cf.check(kernel, "fails", cf.negative, "by decide")
            out[name + label] = {
                "verdict": bool(want),
                "statement": cf.positive if want else cf.negative,
                "accepted": check.accepted,
                "outcome": getattr(check, "outcome", None),
                "axioms": list(check.axioms),
                "reason": check.reason,
                "standard_axioms": set(check.axioms) <= set(STANDARD_AXIOMS),
            }
    checks = [v for k, v in out.items() if not k.startswith("_")]
    out["_unchecked"] = unchecked
    out["_confirmed"] = (bool(checks) and not unchecked
                         and all(v["accepted"] and v["standard_axioms"]
                                 for v in checks))
    return out


def _as_of(day: int) -> str:
    import datetime
    return (datetime.date(1970, 1, 1)
            + datetime.timedelta(days=day)).isoformat() + "T00:00:00"


def candidates(decl: PropertyDecl, rules: dict, model, *,
               max_rows: int = 2, limit: int = 20000) -> Iterator[Candidate]:
    """Generators in cheapest-first order, as the plan specifies."""
    base = list(small_scope(rules, model, max_rows=max_rows, limit=limit))
    if _needs_change(decl):
        # A change-property needs a BEFORE and an AFTER, so the base worlds
        # are the befores and the generators make the change — but only the
        # change the declaration is about. `stable-add` fed a retraction
        # reported a correct rule as broken: a retraction is not an
        # addition, and `stable-retract` is a different claim.
        for cand in base:
            if decl.kind == "stable-add":
                yield from future_dated(cand.ws, rules)
                yield from (c for c in mutants(cand.ws, rules)
                            if c.origin.get("mutator") == "duplicate")
            else:
                yield from (c for c in mutants(cand.ws, rules)
                            if c.origin.get("mutator") == "retract")
        return
    yield from base
    for cand in base:
        yield from mutants(cand.ws, rules)


def search(decl: PropertyDecl, rules: dict, model, *, max_rows: int = 2,
           limit: int = 20000, stop_after: int = 8,
           on_candidate: Callable[[int], None] | None = None,
           ) -> list[Violation]:
    """Distinct violations of `decl`, smallest first, unconfirmed.

    Confirmation is a separate step because it needs a Lean package and
    costs seconds per verdict; the caller decides which of these to spend
    that on.
    """
    found: dict[str, Violation] = {}
    looked = 0
    for cand in candidates(decl, rules, model, max_rows=max_rows,
                           limit=limit):
        looked += 1
        if on_candidate:
            on_candidate(looked)
        if guide.well_formed(cand.ws, model, rules):
            continue
        if _needs_change(decl) and not _change_in_scope(cand, decl):
            continue
        try:
            violated, verdicts, after = screen(cand, decl, rules, model)
        except (KeyError, ValueError):
            continue
        if not violated:
            continue
        small, log = shrink(cand, decl, rules, model)
        sig = signature(small, decl, rules, model)
        if sig in found:
            continue
        v2, verdicts2, after2 = screen(small, decl, rules, model)
        if not v2:                      # shrinking lost it; keep the original
            small, log, verdicts2, after2 = cand, [], verdicts, after
            sig = signature(small, decl, rules, model)
        found[sig] = Violation(
            decl_id=decl.id, kind=decl.kind,
            world={"data": small.ws.data, "subject": small.ws.subject,
                   "as_of_day": small.ws.as_of_day},
            before=({"data": small.before.data,
                     "subject": small.before.subject,
                     "as_of_day": small.before.as_of_day}
                    if small.before else None),
            verdicts=verdicts2, verdicts_after=after2,
            signature=sig, origin=small.origin, shrink_log=log,
            rank=guide.interesting(small.ws, model, rules))
        if len(found) >= stop_after:
            break
    return sorted(found.values(), key=lambda v: (-v.rank, v.signature))
