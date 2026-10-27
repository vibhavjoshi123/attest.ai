"""End-to-end regression for three core fixes, against a real TypeDB server
and the real Lean kernel. Exits non-zero if any expectation fails.

    PYTHONPATH=/path/to/Attest python3 examples/scoping/run.py

1. SCOPED CLOSURE. Samples A and B share the nodes n0..n3; A has opened
   n0→n1, B has opened n1→n2 and n2→n3. "n2 is reachable for A" must be
   proved FALSE, with search and kernel agreeing. Before the fix the search
   walked B's edges too, found a path, the kernel rejected it, and the
   verdict was a DISAGREE that could not be recorded.
2. PARAMETERS. Every decision above is about a (sample, goal) pair, with
   the goal a declared `parameter`, recorded on the decision.
3. DOUBLE NEGATION. "edge e1 is open for A" holds because each of e1's
   criteria has a resolved-true resolution. Retracting one resolution must
   flag that decision; before the fix impact analysis returned nothing.
4. GLOBAL RULE. A rule reading only shared reference facts deploys and
   decides (its search used to leave `$subject` unused, refused by TypeDB).
Plus replay (same snapshot hash and verdict) and recheck from the store,
including a verdict whose proof uses no axioms (recheck used to refuse it:
Lean words that report differently).
"""

from __future__ import annotations

import json
import pathlib
import sys
import uuid

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from attest import (                                           # noqa: E402
    Ingest, Kernel, Store, affected_decisions, decide, govern, ident,
    publish, record, recheck, sync,
)
from domain import ALL, ANY_GOAL, EDGE_OPEN, REACHES, Rule      # noqa: E402

FAILURES: list[str] = []


def expect(cond: bool, what: str) -> None:
    print(f"  {'ok  ' if cond else 'FAIL'} {what}")
    if not cond:
        FAILURES.append(what)


class Clock:
    def __init__(self, at):
        self.at = at

    def __call__(self):
        return self.at


class Seed(Ingest):
    def entities(self):
        self.store.write(
            [f'insert $s isa sample, has sample-id "{s}";' for s in "AB"]
            + [f'insert $n isa node, has node-id "n{i}";' for i in range(4)]
            + [f'insert $e isa edge-def, has edge-id "e{i}";' for i in (1, 2)])

    def fact(self, fid, body):
        self.record(body.replace("{FID}", f'has fact-id "{ident(fid)}", '
                                 f'has source "seed", has recorded-at {{stamp}}'))

    def start(self, fid, s, n):
        self.fact(fid, f'match $s isa sample, has sample-id "{s}"; '
                       f'$n isa node, has node-id "{n}"; '
                       f'insert start-node (sample: $s, node: $n), {{FID}};')

    def goal(self, fid, n):
        self.fact(fid, f'match $n isa node, has node-id "{n}"; '
                       f'insert goal-mark (node: $n), {{FID}};')

    def opened(self, fid, s, a, b):
        self.fact(fid, f'match $s isa sample, has sample-id "{s}"; '
                       f'$a isa node, has node-id "{a}"; '
                       f'$b isa node, has node-id "{b}"; '
                       f'insert open-edge (sample: $s, origin: $a, target: $b), {{FID}};')

    def mark(self, fid, e):
        self.fact(fid, f'match $e isa edge-def, has edge-id "{e}"; '
                       f'insert edge-mark (edge: $e), {{FID}};')

    def criterion(self, fid, e, key):
        self.fact(fid, f'match $e isa edge-def, has edge-id "{e}"; '
                       f'insert criterion (edge: $e), has crit-key "{key}", {{FID}};')

    def resolution(self, fid, s, key, state):
        self.fact(fid, f'match $s isa sample, has sample-id "{s}"; '
                       f'insert resolution (sample: $s), has crit-key "{key}", '
                       f'has state "{state}", {{FID}};')


# facts are stamped just after T0 (the ledger steps past its mark), so
# decisions are taken as of TD, one second later
T0, TD = "2026-10-01T00:00:00", "2026-10-01T00:00:01"
T1, T2 = "2026-10-02T00:00:00", "2026-10-03T00:00:00"


def main() -> int:
    database = f"scoping_{uuid.uuid4().hex[:8]}"
    kernel = Kernel(Rule.lean.directory)
    print(f"kernel: {kernel.version()}")
    with Store(database, scratch=True) as store:
        store.reset(Rule.schema_path)
        for r in ALL:
            sync(store, r)                       # fix 4: any-goal deploys
        artifacts = {r.name: publish(store, r, T0) for r in ALL}
        clock = Clock(T0)
        seed = Seed(store, clock)
        seed.entities()
        seed.start("st-A", "A", "n0")
        seed.start("st-B", "B", "n1")
        for i in range(4):
            seed.goal(f"goal-n{i}", f"n{i}")
        seed.opened("oe-A-01", "A", "n0", "n1")
        seed.opened("oe-B-12", "B", "n1", "n2")
        seed.opened("oe-B-23", "B", "n2", "n3")
        seed.mark("mk-e1", "e1")
        seed.criterion("cr-e1-a", "e1", "e1.a")
        seed.criterion("cr-e1-b", "e1", "e1.b")
        seed.resolution("rs-A-a", "A", "e1.a", "resolved-true")
        seed.resolution("rs-A-b", "A", "e1.b", "resolved-true")
        seed.resolution("rs-B-a", "B", "e1.a", "resolved-true")

        def run(rule, sample, at, **params):
            c = decide(store, rule, sample, at, kernel=kernel, params=params)
            did = None
            if c.verdict != "ERROR" and not c.differential.startswith("DISAGREE"):
                did = record(store, c, rule.subject_type, rule.subject_key, at)
                govern(store, did, artifacts[rule.name])
            return c, did

        print("1-2. scoped closure, decided per (sample, goal) parameter")
        c, d_a1 = run(REACHES, "A", TD, goal="n1")
        expect(c.verdict == "Reaches", "A reaches n1 over its own edge")
        expect(c.differential == "agree", f"search and kernel agree ({c.differential})")
        expect("oe-A-01" in c.relied_on and "oe-B-12" not in c.relied_on,
               f"the path cites A's edge only: {c.relied_on}")
        c, d_a2 = run(REACHES, "A", TD, goal="n2")
        expect(c.verdict == "not Reaches",
               f"A does not reach n2 (B's edges are not A's): {c.verdict}")
        expect(c.differential == "agree",
               f"no DISAGREE from the search walking B's edges ({c.differential})")
        c, _ = run(REACHES, "B", TD, goal="n3")
        expect(c.verdict == "Reaches" and c.differential == "agree",
               "B reaches n3 over its own two edges")
        rows = store.rows(f'match $d isa decision, has decision-id "{d_a1}",'
                          f' has decision-inputs $i; select $i;')
        expect(bool(rows) and json.loads(rows[0]["i"]) == {"goal": "n1"},
               f"the decision records its parameter: {rows}")
        expect(c.snapshot.params == (("goal", "n3"),), "the snapshot carries it")

        print("3. a fact read under two negations is relied on")
        c, d_e1 = run(EDGE_OPEN, "A", TD, edge="e1")
        expect(c.verdict == "EdgeOpen" and c.differential == "agree",
               f"e1 is open for A ({c.verdict}, {c.differential})")
        expect({"rs-A-a", "rs-A-b"} <= set(c.relied_on),
               f"the resolutions are cited: {c.relied_on}")
        cb, _ = run(EDGE_OPEN, "B", TD, edge="e1")
        expect(cb.verdict == "not EdgeOpen", "e1 is not open for B (e1.b unresolved)")
        clock.at = T1
        seed.retract("rs-A-b")
        hit = {h["did"] for h in affected_decisions(store, "rs-A-b",
                                                    Rule.scope_anchors)}
        expect(d_e1 in hit, f"retracting rs-A-b flags the EdgeOpen decision: {hit}")
        c2, _ = run(EDGE_OPEN, "A", T2, edge="e1")
        expect(c2.verdict == "not EdgeOpen", "re-decided after the retraction: closed")

        print("4. a rule over global facts deploys and decides")
        c, _ = run(ANY_GOAL, "A", TD)
        expect(c.verdict == "AnyGoal" and c.differential == "agree",
               f"AnyGoal holds ({c.verdict}, {c.differential})")

        print("replay and recheck")
        c, _ = run(REACHES, "A", TD, goal="n2")
        first = decide(store, REACHES, "A", TD, kernel=kernel, params={"goal": "n2"})
        expect(c.snapshot.sha256 == first.snapshot.sha256
               and c.verdict == first.verdict, "replay: same verdict and snapshot hash")
        # A verdict whose proof uses no axioms at all: before anything is
        # recorded, the edge has no mark, so "not EdgeOpen" is decided over
        # empty lists. Lean reports that as "does not depend on any axioms",
        # which recheck used to read as no report at all and refuse.
        c0, d_empty = run(EDGE_OPEN, "A", T0, edge="e1")
        expect(c0.verdict == "not EdgeOpen"
               and c0.accepted and c0.accepted[0]["axioms"] == [],
               f"an axiom-free verdict ({c0.verdict}, "
               f"axioms {c0.accepted[0]['axioms'] if c0.accepted else '-'})")
        # Each decision is re-checked against the domain that took it:
        # `recheck` re-exports the snapshot itself now, so it needs the rule
        # whose collections the decision was about.
        for did, dom in ((d_a1, REACHES), (d_a2, REACHES),
                         (d_e1, EDGE_OPEN), (d_empty, EDGE_OPEN)):
            r = recheck(store, did, domain=dom)
            expect(r.passed, f"recheck {did}: {r.reason or 'passed'}")

    if FAILURES:
        print(f"\n{len(FAILURES)} expectation(s) FAILED")
        return 1
    print("\nall expectations met")
    return 0


if __name__ == "__main__":
    sys.exit(main())
