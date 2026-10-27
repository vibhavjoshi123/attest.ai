"""Which worlds the store could actually hold.

Tier 1 is a hard, deterministic rejection, and it rejects only what TypeDB
itself would refuse: a value outside `@values`, a missing required field, a
duplicate fact-id, a retraction before the recording, a fact recorded after
the as-of. A search that proposed those would spend kernel time proving
things about states that cannot exist, and would report defects nobody can
hit.

Tier 2 ranks and never deletes. A world that is dirty but possible — two
results on the same day, a row entered in error — is ranked HIGH, because
that is exactly where the interesting defects were: every one of the four
historical fixture defects needed a dirty-but-possible snapshot, and none
of them needed an impossible one.
"""

from __future__ import annotations

from typing import Any


def well_formed(ws, model, rules: dict) -> list[str]:
    """Why the store could not hold this world; `[]` means it could."""
    why: list[str] = []
    seen: dict[str, str] = {}
    for coll, row in ws.rows():
        fid = row.get("fact-id")
        if not fid:
            why.append(f"{coll}: a row with no fact-id")
            continue
        if fid in seen:
            why.append(f"{fid} appears in {seen[fid]} and {coll}")
        seen[fid] = coll
        rec, ret = row.get("recorded-at"), row.get("retracted-at")
        if ret is not None and rec is not None and ret < rec:
            why.append(f"{fid} is retracted at {ret}, before {rec}")
    # a collection the rules read must exist, or every `some` over it is
    # vacuously false and the world says nothing
    for name, rule in rules.items():
        for coll in (c["name"] for c in rule["collections"]):
            if coll not in ws.data:
                why.append(f"{name} reads {coll}, which this world lacks")
    for coll, row in ws.rows():
        for attr, value in row.items():
            spec = model["attributes"].get(attr)
            if not spec:
                continue
            allowed = spec.get("values")
            if allowed and isinstance(value, str) and value not in allowed:
                why.append(f"{row.get('fact-id')}: {attr}={value!r} is "
                           f"outside @values{tuple(sorted(allowed))}")
    return why


def interesting(ws, model, rules: dict | None = None) -> int:
    """A soft rank. Higher is more worth a kernel confirmation.

    Not a filter: nothing is dropped for scoring low. The ranking says
    where to look first, and it points at the dirty-but-possible, because
    that is where the historical defects lived — a same-day pair, an exact
    duplicate from two feeds, a future-dated row.

    WHAT a row's day is comes from `rules` (`generators.day_attributes`):
    with none given, no attribute counts as a date, so only duplicates and
    retractions are ranked. It used to be the literal `taken-day`, one
    domain's name for it, which ranked nothing anywhere else.
    """
    from attest.search.cx.generators import day_attributes

    score = 0
    for coll, rows in ws.data.items():
        dated = day_attributes(rules, coll) if rules else []
        days = [r.get(a) for r in rows for a in dated
                if r.get(a) is not None]
        if len(days) != len(set(days)):
            score += 3                       # a same-day tie
        bare = [tuple(sorted((k, v) for k, v in r.items()
                             if k not in ("fact-id", "source", "recorded-at")))
                for r in rows]
        if len(bare) != len(set(bare)):
            score += 3                       # the same reading twice
        if any(d is not None and d > ws.as_of_day for d in days):
            score += 2                       # dated after the decision
        if any(r.get("retracted-at") for r in rows):
            score += 1
    return score
