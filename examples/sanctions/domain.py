"""The sanctions-screening domain: a second rule on the same, unchanged core."""
from __future__ import annotations

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from common import facts  # noqa: E402

from attest.domain import LeanPackage  # noqa: E402
from attest.runner import make_snapshot  # noqa: E402
from attest.store import dt, ident  # noqa: E402


class Sanctions:
    schema_path = HERE / "schema.tql"
    rule_path = HERE / "sanctions.rule"
    lean = LeanPackage(directory=HERE / "lean", root_module="Sanctions",
                       schema_namespace="Sanctions.Schema",
                       rules_namespace="Sanctions.Rules")
    subject_type, subject_key = "party", "lei"

    scope_anchors = (
        '$f isa engagement, has fact-id "{fid}", links (vendor: $x);'
        ' coverage (decision: $d, item: $x);',
        '$f isa ownership, has fact-id "{fid}", links (owned: $x);'
        ' coverage (decision: $d, item: $x);',
        '$f isa listing, has fact-id "{fid}", links (party: $x);'
        ' coverage (decision: $d, item: $x);',
    )

    def subjects(self, store, as_of):
        return sorted(r["l"] for r in store.rows(
            "match $x isa party, has lei $l; select $l;"))

    def snapshot(self, store, subject, as_of):
        lei, t = ident(subject), dt(as_of)
        with store.read() as tx:
            store.require(tx, f'$x isa party, has lei "{lei}";',
                          f"no party {lei!r}")
            engagements = facts(
                store, tx, "$g",
                f'$v isa party, has lei "{lei}"; $v has lei $vl;'
                f' $g isa engagement, links (vendor: $v);',
                {"vendor": "$vl"}, {"contract-ref": "$cr"}, t)
            # Walk owners one level at a time.
            seen, frontier, owns = {lei}, [lei], []
            while frontier:
                nxt = []
                for x in frontier:
                    for o in facts(
                            store, tx, "$o",
                            f'$a isa party, has lei "{ident(x)}"; $a has lei $al;'
                            f' $o isa ownership, links (owned: $a, owner: $b);'
                            f' $b has lei $bl;',
                            {"owned": "$al", "owner": "$bl"}, {}, t):
                        owns.append(o)
                        if o["owner"] not in seen:
                            seen.add(o["owner"])
                            nxt.append(o["owner"])
                frontier = sorted(nxt)
            listings = []
            for x in sorted(seen):
                listings += facts(
                    store, tx, "$l",
                    f'$p isa party, has lei "{ident(x)}"; $p has lei $pl;'
                    f' $l isa listing, links (party: $p);',
                    {"party": "$pl"},
                    {"regime": "$rg", "list-status": "$ls"}, t)
        data = {"engagements": engagements,
                "ownerships": sorted(owns, key=lambda r: r["fact-id"]),
                "listings": sorted(listings, key=lambda r: r["fact-id"])}
        ids = sorted(r["fact-id"] for rows in data.values() for r in rows)
        scope = [("party", "lei", p) for p in sorted(seen)]
        return make_snapshot(lei, t, data, fact_ids=ids, scope=scope)

    def scope(self, snapshot):
        return list(snapshot.scope)


class SanctionsIngest:
    def __init__(self, ingest):
        self.ingest = ingest

    def engage(self, fid, vendor, contract, source):
        return self.ingest.record(
            f'match $v isa party, has lei "{ident(vendor)}";'
            f' insert $f isa engagement, links (vendor: $v),'
            f' has contract-ref "{ident(contract)}",'
            f' has fact-id "{ident(fid)}", has source "{ident(source)}",'
            f' has recorded-at {{stamp}};')

    def owns(self, fid, owned, owner, source):
        return self.ingest.record(
            f'match $a isa party, has lei "{ident(owned)}";'
            f' $b isa party, has lei "{ident(owner)}";'
            f' insert $f isa ownership, links (owned: $a, owner: $b),'
            f' has fact-id "{ident(fid)}", has source "{ident(source)}",'
            f' has recorded-at {{stamp}};')

    def list(self, fid, party, regime, status, source):
        return self.ingest.record(
            f'match $p isa party, has lei "{ident(party)}";'
            f' insert $f isa listing, links (party: $p),'
            f' has regime "{ident(regime)}", has list-status "{ident(status)}",'
            f' has fact-id "{ident(fid)}", has source "{ident(source)}",'
            f' has recorded-at {{stamp}};')
