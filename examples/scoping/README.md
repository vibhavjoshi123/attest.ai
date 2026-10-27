# scoping — regression domain for parameters, scoped closures and reliance

A deliberately small, abstract domain. Nodes and edge definitions are shared;
each sample opens its own edges and records its own resolutions, the way one
route map is shared by many travellers.

| Rule | What it checks in the core |
|---|---|
| `scoping.reaches` | a **parameter** (`goal`) and a **closure over a scoped collection**: sample A must not reach a node through sample B's edges |
| `scoping.edge-open` | a fact read under **two negations** is relied on, so retracting it flags the decision |
| `scoping.any-goal` | a rule over **global facts only** deploys (its search used to leave `$subject` unused) |

`run.py` runs everything live against TypeDB and the Lean kernel and exits
non-zero on any failed expectation, including replay and `recheck` of an
**axiom-free** verdict (which recheck used to refuse). It is a stage of
`scripts/examples.sh`.

```
PYTHONPATH=/path/to/Attest python3 examples/scoping/run.py
```
