"""One world, read by several rules at once.

A declared property is about a set of rules over the SAME snapshot, so the
search needs a world the whole family can be evaluated on. `world.Case` is
per-rule, and the rules of a family share a subject and their collections,
so a single data dict feeds one `Case` per rule.

Verdicts come from the reference evaluator in microseconds. They are a
screen, not an answer: whatever this flags is handed to the kernel.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import Any

from attest.search import world


@dataclass
class WorldSet:
    """A snapshot and the rules read over it."""

    data: dict[str, list[dict[str, Any]]]
    subject: str = "s1"
    as_of_day: int = 20000
    params: dict[str, str] = field(default_factory=dict)

    def case(self, rule, model) -> world.Case:
        return world.Case(rule, model, copy.deepcopy(self.data), self.subject,
                          dict(self.params), as_of_day=self.as_of_day)

    def verdicts(self, rules: dict, model) -> dict[str, bool]:
        """Which of `rules` (short name -> parsed rule) hold here."""
        return {name: bool(self.case(rule, model).witnesses())
                for name, rule in rules.items()}

    def rows(self) -> list[tuple[str, dict]]:
        return [(coll, row) for coll, rs in self.data.items() for row in rs]

    def copy(self) -> "WorldSet":
        return WorldSet(copy.deepcopy(self.data), self.subject,
                        self.as_of_day, dict(self.params))

    def without(self, coll: str, fact_id: str) -> "WorldSet":
        out = self.copy()
        out.data[coll] = [r for r in out.data[coll]
                          if r.get("fact-id") != fact_id]
        return out

    def size(self) -> int:
        return sum(len(rs) for rs in self.data.values())

    def widest(self) -> int:
        return max((len(rs) for rs in self.data.values()), default=0)


#: ---------------------------------------------------------------- filters
#: a `when` filter that is about a row's relation to the OTHERS, not
#: about its own field values: the row re-states one already present.
#: Routine — feed overlap and re-ingestion — and the shape of the
#: second historical defect, where a duplicate silenced a stop rule.
DUPLICATE = "duplicate"


def matches_when(row: dict, when: str | None, as_of_day: int) -> bool:
    """Does `row` satisfy a declaration's `when` clause?

    A `stable-*` declaration restricts WHICH rows it is about: fixture's
    says `when taken-day > as-of-day`, i.e. only rows dated after the
    decision. Without this the claim reads as "no added row ever changes a
    verdict", which is false of every working rule — a new alpha reading is
    *supposed* to change the answer. Skipping the filter made the search
    report correct rules as broken, which is worse than finding nothing.

    The syntax is the rule language's `require` right-hand side, so
    `as-of-day`, `as-of-day - 180` and a bare integer all appear.
    """
    if not when:
        return True
    if when.strip() == DUPLICATE:
        # handled by the caller, which can see the rest of the world
        return True
    parts = when.split()
    if len(parts) < 3:
        raise ValueError(f"cannot read `when {when}`")
    attr, op, rhs = parts[0], parts[1], " ".join(parts[2:])
    if attr not in row or row[attr] is None:
        return False
    want = _rhs(rhs, as_of_day)
    left = row[attr]
    if op == ">":
        return left > want
    if op == ">=":
        return left >= want
    if op == "<":
        return left < want
    if op == "<=":
        return left <= want
    if op == "=":
        return left == want
    if op == "!=":
        return left != want
    raise ValueError(f"cannot read the operator in `when {when}`")


def _rhs(text: str, as_of_day: int):
    from attest.search.world import AS_OF_RE

    m = AS_OF_RE.match(text.strip())
    if m:
        sign, num = m.group(1), m.group(2)
        return as_of_day + (int(num or 0) * (-1 if sign == "-" else 1))
    try:
        return int(text)
    except ValueError:
        return text.strip().strip('"')


def same_reading(a: dict, b: dict) -> bool:
    """Do two rows say the same thing, differing only in bookkeeping?

    Provenance is excluded on purpose: two feeds reporting one result give
    different fact-ids, sources and recording times, and the whole point of
    the claim is that such a pair is ONE reading.
    """
    keep = lambda r: {k: v for k, v in r.items()
                      if k not in ("fact-id", "source", "recorded-at",
                                   "retracted-at")}
    return keep(a) == keep(b)
