"""A small regression domain for three core fixes (see schema.tql).

The export is generic over the rule's own collections: for each one it reads
the declared relation type, scoped to the subject or to a parameter exactly
as the collection line says. Trusted code, so it stays plain lookups.
"""

from __future__ import annotations

import pathlib

from attest import LeanPackage, Snapshot, as_of, dt, ident, make_snapshot, rulec

HERE = pathlib.Path(__file__).resolve().parent
RULES = HERE.parent / "rules" / "scoping"

#: role -> (player type, key attribute), and owned attributes, per relation
SHAPES = {
    "start-node": ({"sample": ("sample", "sample-id"),
                    "node": ("node", "node-id")}, []),
    "goal-mark": ({"node": ("node", "node-id")}, []),
    "open-edge": ({"sample": ("sample", "sample-id"),
                   "origin": ("node", "node-id"),
                   "target": ("node", "node-id")}, []),
    "edge-mark": ({"edge": ("edge-def", "edge-id")}, []),
    "criterion": ({"edge": ("edge-def", "edge-id")}, ["crit-key"]),
    "resolution": ({"sample": ("sample", "sample-id")}, ["crit-key", "state"]),
}


class Rule:
    schema_path = HERE / "schema.tql"
    subject_type = "sample"
    subject_key = "sample-id"
    lean = LeanPackage(directory=HERE / "lean", root_module="Scoping",
                       schema_namespace="Scoping.Schema",
                       rules_namespace="Scoping.Rules")
    scope_anchors = (
        '$e isa resolution, has fact-id "{fid}", links (sample: $x);'
        ' coverage (decision: $d, item: $x);',
        '$e isa open-edge, has fact-id "{fid}", links (sample: $x);'
        ' coverage (decision: $d, item: $x);',
        '$e isa criterion, has fact-id "{fid}", links (edge: $x);'
        ' coverage (decision: $d, item: $x);',
    )

    def __init__(self, name: str):
        self.name = name
        self.rule_path = RULES / f"{name}.rule"
        self.rule = rulec.load(self.rule_path)

    def subjects(self, store, at):
        return sorted(r["k"] for r in store.rows(
            "match $s isa sample, has sample-id $k; select $k;"))

    def snapshot(self, store, subject, at, params=None) -> Snapshot:
        subject, at = ident(subject), dt(at)
        params = {k: ident(v) for k, v in (params or {}).items()}
        types = {p["name"]: p["type"] for p in self.rule["params"]}
        keys = {"sample": "sample-id", "node": "node-id",
                "edge-def": "edge-id"}
        data, scope = {}, [("sample", "sample-id", subject)]
        for p, v in params.items():
            scope.append((types[p], keys[types[p]], v))
        with store.read() as tx:
            store.require(tx, f'$x isa sample, has sample-id "{subject}";',
                          f"no sample {subject!r}")
            for c in self.rule["collections"]:
                roles, attrs = SHAPES[c["type"]]
                where = ""
                if c["via"]:
                    sc = c["scope"] or "subject"
                    val = subject if sc == "subject" else params[sc]
                    _ptype, pkey = roles[c["via"]]
                    # constrain the role's own player: a second
                    # `links (role: $other)` would ask for a second player
                    where = f' ${c["via"].replace("-", "")} has {pkey} "{val}";'

                links = ", ".join(f"{role}: ${role.replace('-', '')}"
                                  for role in roles)
                keyed = "".join(f" ${role.replace('-', '')} has {key}"
                                f" ${role.replace('-', '')}k;"
                                for role, (_t, key) in roles.items())
                owned = "".join(f" has {a} ${a.replace('-', '')}," for a in attrs)
                sel = ([f"${r.replace('-', '')}k" for r in roles]
                       + [f"${a.replace('-', '')}" for a in attrs]
                       + ["$f", "$s", "$ra_r"])
                rows = store.lookup(
                    tx,
                    f"$r isa {c['type']}, links ({links});{where}"
                    f" {as_of('$r', at)}",
                    f"$r{owned} has fact-id $f, has source $s;{keyed}",
                    ", ".join(sel), "$r")
                out = []
                for x in rows:
                    row = {role: x[f"{role.replace('-', '')}k"] for role in roles}
                    row.update({a: x[a.replace('-', '')] for a in attrs})
                    row.update({"fact-id": x["f"], "source": x["s"],
                                "recorded-at": x["ra_r"][:19],
                                "retracted-at": None})
                    out.append(row)
                data[c["name"]] = out
        fact_ids = sorted({r["fact-id"] for rows in data.values() for r in rows})
        return make_snapshot(subject, at, data, fact_ids=fact_ids,
                             scope=scope, params=params)

    def scope(self, snapshot):
        return list(snapshot.scope)


REACHES = Rule("reaches")
EDGE_OPEN = Rule("edge-open")
ANY_GOAL = Rule("any-goal")
ALL = (REACHES, EDGE_OPEN, ANY_GOAL)
