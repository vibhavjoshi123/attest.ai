"""Where candidate worlds come from.

A measurement sets the design: on a rule family whose rules need several
specific rows at once, random generation never made two of the rules hold
at all — 0 of 3,000 seeds — while small-scope enumeration found the first
historical defect in milliseconds. So the cheap, systematic generators run first and random
generation is the fallback, not the strategy.

Two generators here, in cheapest-first order:

* **small scope** enumerates every world of at most a few rows per
  collection, drawing each field from the values the rules actually
  mention. Defects about "latest", ties and `none of` blocks live at two
  rows, and two rows is a space small enough to exhaust.
* **mutators** take a world where a rule already holds and break one thing
  about it — move a row to another subject, retract it, duplicate it under
  a new fact-id. These are the ones that find scope and provenance defects,
  which no amount of fresh generation reaches because it never produces the
  witness in the first place.
"""

from __future__ import annotations

import itertools
import random
from dataclasses import dataclass
from typing import Any, Iterator

from attest import rulec
from attest.search import world
from attest.search.cx.world_set import WorldSet


@dataclass(frozen=True)
class Candidate:
    """A world, how it was made, and what change it represents."""

    ws: WorldSet
    origin: dict
    #: for the `stable-*` kinds: the world before the change
    before: WorldSet | None = None


def _partition(rule, model, coll_type: str) -> dict[str, list[Any]]:
    """For each field, the values worth trying.

    The literals the rules compare against, each threshold and one value
    either side of it, because a defect about `>= 70` shows up at 69, 70
    and 71 and nowhere else. Enumerating the whole integer range would be
    the same search a thousand times over.
    """
    out: dict[str, list[Any]] = {}
    for tname, lean_field, _lean_type, how in __import__(
            "attest.typebridge", fromlist=["fields"]).fields(model, coll_type):
        if tname in ("fact-id", "source", "recorded-at", "retracted-at"):
            continue
        spec = model["attributes"].get(tname, {})
        if spec.get("values"):
            out[tname] = sorted(spec["values"])
            continue
        lits = sorted({v for v in _int_literals(rule, tname)})
        if lits:
            vals = set()
            for v in lits:
                vals.update({v - 1, v, v + 1})
            out[tname] = sorted(vals)
        else:
            out[tname] = [0, 1]
    return out


def _int_literals(rule, attr: str) -> list[int]:
    """Every integer this rule compares `attr` against, as-of-relative
    offsets resolved to absolute days."""
    found: list[int] = []
    for step in rulec.all_steps(rule["steps"]):
        if step["kind"] != "require":
            continue
        lhs, rhs = step.get("lhs", ""), step.get("rhs", "")
        if not lhs.endswith("." + attr):
            continue
        m = world.AS_OF_RE.match(rhs.strip())
        if m:
            sign, num = m.group(1), m.group(2)
            off = int(num or 0) * (-1 if sign == "-" else 1)
            found.append(20000 + off)
        else:
            try:
                found.append(int(rhs))
            except (TypeError, ValueError):
                continue
    return found


def small_scope(rules: dict, model, *, max_rows: int = 2,
                limit: int = 20000) -> Iterator[Candidate]:
    """Every world of up to `max_rows` rows per collection.

    The rows are drawn from the partitioned field values, so this is
    exhaustive over the shapes the rules can distinguish rather than over
    all possible data.
    """
    rule = next(iter(rules.values()))
    colls = {c["name"]: c["type"] for c in rule["collections"]}
    if not colls:
        return
    made = 0
    for name, ctype in colls.items():
        part = _partition(rule, model, ctype)
        fields = sorted(part)
        rows = [dict(zip(fields, combo))
                for combo in itertools.product(*(part[f] for f in fields))]
        for count in range(1, max_rows + 1):
            for chosen in itertools.combinations_with_replacement(rows, count):
                data = {c: [] for c in colls}
                data[name] = [
                    {**row, "fact-id": f"f{i:03d}", "source": "src",
                     "recorded-at": "2026-01-01T00:00:00",
                     "retracted-at": None,
                     **_scope_fields(rule, name)}
                    for i, row in enumerate(chosen, 1)]
                made += 1
                if made > limit:
                    return
                yield Candidate(
                    ws=WorldSet(data=data),
                    origin={"generator": "small-scope", "collection": name,
                            "rows": count})


def _scope_fields(rule, coll_name: str) -> dict:
    """The `via` role a scoped collection needs, set to the subject."""
    for c in rule["collections"]:
        if c["name"] == coll_name and c.get("via"):
            return {c["via"]: "s1"}
    return {}


#: each mutator takes a world and a row, and returns a changed world
def _foreign_subject(ws, coll, row, rule):
    via = next((c.get("via") for c in rule["collections"]
                if c["name"] == coll), None)
    if not via or row.get(via) is None:
        return None
    out = ws.copy()
    for r in out.data[coll]:
        if r.get("fact-id") == row.get("fact-id"):
            r[via] = "someone-else"
    return out, {"mutator": "foreign-subject", "fact-id": row.get("fact-id")}


def _retract(ws, coll, row, rule):
    if row.get("retracted-at"):
        return None
    out = ws.copy()
    for r in out.data[coll]:
        if r.get("fact-id") == row.get("fact-id"):
            r["retracted-at"] = "2026-06-01T00:00:00"
    return out, {"mutator": "retract", "fact-id": row.get("fact-id")}


def _duplicate(ws, coll, row, rule):
    out = ws.copy()
    fresh = dict(row)
    fresh["fact-id"] = f"{row.get('fact-id')}-dup"
    out.data[coll].append(fresh)
    return out, {"mutator": "duplicate", "fact-id": row.get("fact-id"),
                 "as": fresh["fact-id"]}


MUTATORS = (_foreign_subject, _retract, _duplicate)


def mutants(ws: WorldSet, rules: dict) -> Iterator[Candidate]:
    """Every one-step mutation of `ws`.

    Applied to a world where something already holds, these are what find
    scope and provenance defects: a rule that forgot to check whose record
    it is reads a foreign row as its own, and no fresh generation finds
    that because it never builds the witness to begin with.
    """
    rule = next(iter(rules.values()))
    for coll, row in ws.rows():
        for mutator in MUTATORS:
            made = mutator(ws, coll, row, rule)
            if made is None:
                continue
            out, origin = made
            yield Candidate(ws=out, origin={"generator": "mutator", **origin},
                            before=ws)


def day_attributes(rules: dict, coll: str) -> list[str]:
    """The attributes of `coll`'s rows that some rule compares with
    `as-of-day`: what "dated" means for that collection, read from the rules
    rather than assumed from one domain's attribute name."""
    from attest.rulec import AS_OF_DAY

    found: set[str] = set()

    def walk(steps, binders):
        binders = dict(binders)
        for s in steps:
            if s["kind"] == "some":
                binders[s["var"]] = s["coll"]
            elif s["kind"] == "none":
                walk(s["steps"], binders)
            elif s["kind"] == "require":
                sides = (s.get("lhs", ""), s.get("rhs", ""))
                if not any(str(x).strip().startswith(AS_OF_DAY)
                           for x in sides):
                    continue
                for x in sides:
                    var, _, attr = str(x).strip().partition(".")
                    if attr and binders.get(var) == coll:
                        found.add(attr)

    for rule in rules.values():
        walk(rule["steps"], {})
    return sorted(found)


def future_dated(ws: WorldSet, rules: dict) -> Iterator[Candidate]:
    """`stable-add` candidates: the same world plus one row dated after the
    decision.

    This is the change a `stable-add … when <day> > as-of-day` declaration
    says must not matter, so the generator for it adds exactly that row
    rather than searching for it.

    WHICH attribute is the row's date comes from the rules: every attribute
    of a binder over the collection that some rule compares with
    `as-of-day` (`day_attributes`). It used to be the literal
    `effective-day`, one domain's name for it, so in any domain that called
    its date anything else the "future" row carried an extra key nothing
    read, and every candidate this generator produced was the old world in
    disguise.
    """
    rule = next(iter(rules.values()))
    for c in rule["collections"]:
        coll = c["name"]
        if coll not in ws.data or not ws.data[coll]:
            continue
        days = day_attributes(rules, coll)
        if not days:
            continue                     # nothing in it is dated
        template = dict(ws.data[coll][0])
        for offset, value in ((1, None), (365, None)):
            out = ws.copy()
            row = dict(template)
            row["fact-id"] = f"future-{offset}"
            for attr in days:
                row[attr] = ws.as_of_day + offset
            out.data[coll].append(row)
            yield Candidate(
                ws=out, before=ws,
                origin={"generator": "future-dated", "collection": coll,
                        "days-after": offset})
