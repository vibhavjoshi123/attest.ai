"""A reference evaluator for the rule language, and random snapshots for it.

Test infrastructure, and deliberately NOT trusted: nothing in `attest/`
imports it. It exists to give the offline tests an independent statement of
what a rule means, so that

  * the compiler refactor can be pinned to the outputs it had before, on
    snapshots that actually contain witnesses;
  * impact analysis can be property-tested: retract or add a fact, re-decide,
    and check every verdict flip was predicted;
  * with Lean installed, the generated Lean definitions can be checked to
    agree with it on the same snapshots — a third opinion on what each rule
    says, independent of both compiled forms.

It reads the PARSED rule (the dicts `rulec.parse` returns) and the schema
model, and evaluates the semantics the Lean definition has: every binder is
guarded by its collection's scope and by non-retraction; a closure is
reflexive and walks only unretracted (and, when scoped, in-scope) edges;
`none of` is the negation of an existential.
"""

from __future__ import annotations

import random
import re
from typing import Any, Iterator

from attest import rulec, typebridge as tb

AS_OF_RE = re.compile(r"^as-of-day(?:\s*([-+])\s*(\d+))?$")


# ─────────────────────────────────────────────────────────── evaluation
class Case:
    """One snapshot: rows per collection, the scope keys and the day."""

    def __init__(self, rule, model, data, subject, params=None,
                 as_of_day=20000):
        self.rule, self.model, self.data = rule, model, data
        self.scopes = {"subject": subject, **(params or {})}
        self.as_of_day = as_of_day
        self.colls = {c["name"]: c for c in rule["collections"]}
        self.closures = {c["name"]: c for c in rule["closures"]}

    # a binder ranges over its collection's rows that pass the guards
    def rows(self, coll: str) -> list[dict]:
        c = self.colls[coll]
        out = []
        for row in self.data[coll]:
            if row.get("retracted-at") is not None:
                continue
            if c["via"] and row[c["via"]] != self.scopes[c["scope"] or "subject"]:
                continue
            out.append(row)
        return out

    def reach(self, closure: str, start: str) -> set[str]:
        clo = self.closures[closure]
        c = self.colls[clo["coll"]]
        edges = [e for e in self.data[clo["coll"]]
                 if e.get("retracted-at") is None
                 and (not c["via"]
                      or e[c["via"]] == self.scopes[c["scope"] or "subject"])]
        seen, todo = {start}, [start]
        while todo:
            x = todo.pop()
            for e in edges:
                if e[clo["from"]] == x and e[clo["to"]] not in seen:
                    seen.add(e[clo["to"]])
                    todo.append(e[clo["to"]])
        return seen

    def value(self, expr: str, env: dict[str, dict], other: str | None):
        expr = expr.strip()
        m = AS_OF_RE.match(expr)
        if m:
            off = int(m.group(2) or 0) * (-1 if m.group(1) == "-" else 1)
            return self.as_of_day + off
        if "." in expr:
            v, f = expr.split(".", 1)
            return env[v][f]
        lit = expr.strip('"')
        # a literal compared with an integer field is an integer
        if other is not None and "." in other:
            v, f = other.strip().split(".", 1)
            if isinstance(env[v][f], int) and re.fullmatch(r"-?\d+", lit):
                return int(lit)
        return lit

    def cond(self, s, env) -> bool:
        a = self.value(s["lhs"], env, s["rhs"])
        b = self.value(s["rhs"], env, s["lhs"])
        op = s["op"]
        if op not in rulec.COMPARISONS:
            return b in self.reach(s["closure"], a)
        return {"=": a == b, "!=": a != b, ">=": a >= b, "<=": a <= b,
                ">": a > b, "<": a < b}[op]

    def solutions(self, steps, env, witness=True) -> Iterator[tuple]:
        """Every way to satisfy `steps`, as the tuple of top-level rows."""
        if not steps:
            yield ()
            return
        s, rest = steps[0], steps[1:]
        if s["kind"] == "some":
            for row in self.rows(s["coll"]):
                for tail in self.solutions(rest, {**env, s["var"]: row},
                                           witness):
                    yield ((row["fact-id"],) if witness else ()) + tail
        elif s["kind"] == "none":
            if not any(True for _ in self.solutions(s["steps"], dict(env),
                                                    False)):
                yield from self.solutions(rest, env, witness)
        else:
            if self.cond(s, env):
                yield from self.solutions(rest, env, witness)

    def witnesses(self) -> list[list[str]]:
        return sorted({tuple(w) for w in self.solutions(self.rule["steps"], {})})

    def holds(self) -> bool:
        return bool(self.witnesses())


# ──────────────────────────────────────────────────────── random snapshots
def _literals(rule) -> dict[str, list]:
    """Values the rule mentions, so a random snapshot can satisfy it."""
    strs, ints = set(), set()
    for s in rulec.all_steps(rule["steps"]):
        if s["kind"] != "require":
            continue
        for side in (s["lhs"], s["rhs"]):
            side = side.strip()
            m = AS_OF_RE.match(side)
            if m:
                off = int(m.group(2) or 0) * (-1 if m.group(1) == "-" else 1)
                ints.update({20000 + off - 1, 20000 + off, 20000 + off + 1})
            elif "." not in side:
                lit = side.strip('"')
                if re.fullmatch(r"-?\d+", lit):
                    n = int(lit)
                    ints.update({n - 1, n, n + 1})
                else:
                    strs.add(lit)
    return {"str": sorted(strs), "int": sorted(ints) or [0, 1, 2]}


def _row(c, model, rng, lits, keys, scopes, fid) -> dict[str, Any]:
    """One random row of collection `c`."""
    row: dict[str, Any] = {}
    for (an, _f, _ty, how) in tb.fields(model, c["type"]):
        base = how.rstrip("?")
        if how.endswith("?") and rng.random() < 0.3:
            row[an] = None
        elif an == "fact-id":
            row[an] = fid
        elif an in ("recorded-at",):
            row[an] = "2026-01-01T00:00:00"
        elif an == "retracted-at":
            row[an] = None
        elif an == "source":
            row[an] = "src"
        elif base == "role1":
            if c["via"] == an:
                row[an] = (scopes[c["scope"] or "subject"]
                           if rng.random() < 0.8 else "s2")
            else:
                row[an] = rng.choice(keys)
        elif base == "roleN":
            row[an] = rng.sample(keys, rng.randint(0, 2))
        elif base == "enum":
            row[an] = rng.choice(model["attributes"][an]["values"])
        elif base == "int":
            row[an] = rng.choice(lits["int"])
        else:
            row[an] = rng.choice(lits["str"] + ["x", "y"]
                                 if lits["str"] else ["x", "y"])
    return row


def _keys(rule):
    return ["s1", "s2", "k1", "k2", "k3"] + _literals(rule)["str"]


def random_case(rule, model, rng: random.Random, *, size=4,
                subject="s1") -> Case:
    """A random snapshot for `rule`, biased toward values it mentions."""
    lits = _literals(rule)
    keys = _keys(rule)
    params = {p["name"]: rng.choice(["k1", "k2"]) for p in rule["params"]}
    scopes = {"subject": subject, **params}
    data, n = {}, 0
    for c in rule["collections"]:
        rows = []
        for _ in range(rng.randint(0, size)):
            n += 1
            rows.append(_row(c, model, rng, lits, keys, scopes, f"f{n:03d}"))
        data[c["name"]] = rows
    return Case(rule, model, data, subject, params)


def add(case: Case, coll: str, rng: random.Random) -> Case:
    """The same case with one more random fact in `coll`, as a fact recorded
    later — and in scope — would make it."""
    c = case.colls[coll]
    row = _row(c, case.model, rng, _literals(case.rule), _keys(case.rule),
               case.scopes, f"new{rng.randrange(10**6):06d}")
    data = {k: list(rows) for k, rows in case.data.items()}
    data[coll].append(row)
    return Case(case.rule, case.model, data, case.scopes["subject"],
                {k: v for k, v in case.scopes.items() if k != "subject"},
                case.as_of_day)


def drop(case: Case, fact_id: str) -> Case:
    """The same case with one fact gone, as a retraction makes it."""
    data = {k: [r for r in rows if r.get("fact-id") != fact_id]
            for k, rows in case.data.items()}
    return Case(case.rule, case.model, data, case.scopes["subject"],
                {k: v for k, v in case.scopes.items() if k != "subject"},
                case.as_of_day)
