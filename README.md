# Attest

A verification layer over TypeDB and Lean 4. **TypeDB finds, Lean checks,
TypeDB remembers.**

A rule is written once, in a small declarative language, and compiled into two
programs: a **Lean definition**, which is the authority, and a **TypeQL
function**, which is a fast but untrusted way to find candidates. TypeDB
searches for facts that might satisfy the rule; the Lean kernel re-derives the
result from a hashed snapshot of those facts and refuses anything that does
not follow. The verdict, the proof, the snapshot hash, and the exact rule and
type artifacts it was checked against all go back into TypeDB, so any decision
can be re-verified later from storage alone.

The only component that has to be trusted completely is Lean's kernel — about
5,400 lines of C++. Everything else, TypeDB included, is checked.

For why the work is split across two systems, in terms of what each one
actually does internally, see [docs/WHY_TWO_SYSTEMS.md](docs/WHY_TWO_SYSTEMS.md).

## What is in this repository

This repository is the **core only**: `attest/`. It contains nothing about any
particular subject matter, and it never will — a domain is supplied from
outside it.

| File | What it does |
|---|---|
| `attest/core.tql` | the domain-neutral TypeDB schema: facts, sources, ledger times, decisions, proofs, artifacts, reliance and coverage edges |
| `attest/domain.py` | the `Domain` protocol — everything a caller must supply, and nothing more |
| `attest/rulec.py` | the rule compiler: one `.rule` file to a Lean definition and a TypeQL function |
| `attest/typebridge.py` | reads the live TypeDB schema and generates the matching Lean types |
| `attest/kernel.py` | the trust boundary: runs Lean, accepts only a clean proof with allow-listed axioms |
| `attest/store.py` | TypeDB access, the single ingestion door, and the as-of ledger |
| `attest/runner.py` | the decision path: `sync`, `publish`, `search`, `decide`, `record`, `govern`, `recheck`, and impact analysis |
| `attest/config.py` | connection settings from the environment |
| `tests/` | the core's own tests, run against a small built-in fixture domain (see [Tests](#tests)) |

## Requirements

- **Python** 3.11+
- **Lean 4** on `PATH`. Tested with v4.35.0. Each Lake package pins its own
  toolchain in `lean-toolchain`, and the version that checked a proof is
  recorded in the certificate.
- **TypeDB 3** server, and the matching driver:

  ```
  pip install typedb-driver==3.13.6
  ```

  The driver and the server must agree on the network protocol version.
  Driver 3.8.0 implements protocol 7.1 and a 3.12+ server requires 8.2, so an
  older driver is refused at connect time rather than failing later.

### Connecting

Read from the environment by `attest.StoreConfig`:

| Variable | Meaning |
|---|---|
| `TYPEDB_ADDRESS` | e.g. `127.0.0.1:1729`, or an `https://` URL |
| `TYPEDB_USERNAME`, `TYPEDB_PASSWORD` | credentials |
| `TYPEDB_TLS` or `TYPEDB_TLS_ENABLED` | `1` for TLS; implied by an `https://` address |
| `TYPEDB_TLS_ROOT_CA` | optional CA path |

A local server for development:

```bash
typedb server --diagnostics.reporting.metrics false
export TYPEDB_ADDRESS=127.0.0.1:1729
export TYPEDB_USERNAME=admin TYPEDB_PASSWORD=password
```

Those are the server's defaults and are not production settings — see §7 of
[docs/WHY_TWO_SYSTEMS.md](docs/WHY_TWO_SYSTEMS.md).

## Running a domain against this repository

A domain lives in its own folder, outside this one, and supplies four things.
Put this repository on `PYTHONPATH` (or install it) and `import attest`.

**1. A schema** (`schema.tql`) declaring what facts exist. It is loaded on top
of `attest/core.tql`, so every fact type inherits `fact-id`, `source`,
`recorded-at` and `retracted-at` without restating them.

**2. A rule** (`<name>.rule`), written once:

```
rule acme.flagged v0.1
says "A subject is flagged if its latest reading is at or above 70."

subject item

collection readings : reading for subject via item

conclude Flagged when
  some reading a in readings
  require a.value >= 70
  require a.effective-day >= as-of-day - 180
  require a.effective-day <= as-of-day
  none of
    some reading n in readings
    require n.fact-id != a.fact-id
    require n.effective-day > a.effective-day
    require n.effective-day <= as-of-day
```

Note that the rule says what *latest* means. If the export handed over only
the newest reading, "latest" would be true by construction and nothing would
check it. The trusted part stays dumb.

**3. A Lean package** — a Lake package whose generated modules the compiler
writes into, declared with `attest.LeanPackage`.

**4. A class implementing `attest.Domain`:** `schema_path`, `rule_path`,
`lean`, `subject_type`, `subject_key`, a `snapshot()` that reads one case out
of the store with simple non-recursive queries, `scope()`, and
`scope_anchors`. See the docstrings in `attest/domain.py`, which spell out
what each one is for and what goes wrong without it.

Nothing else. The search, the Lean definition of the rule, the proof term, the
Lean types, and the list of facts a verdict relied on are all generated — a
domain cannot make the two sides disagree, because it does not write either of
them.

### The decision path

```python
import os
from attest import Store, Kernel, sync, publish, decide, record, govern, recheck
from acme.domain import Acme                    # your domain

dom = Acme()
kernel = Kernel(dom.lean.directory)

with Store(os.environ.get("TYPEDB_DATABASE", "acme")) as store:
    store.reset(dom.schema_path)                # core.tql + your schema
    sync(store, dom)                            # compile the rule both ways,
                                                # generate Lean types, check drift
    artifacts = publish(store, dom, "2026-01-01T00:00:00")  # store them, hashed

    # ... record facts through attest.Ingest ...

    cert = decide(store, dom, "item-1", "2026-02-01T00:00:00", kernel=kernel)
    print(cert.verdict, cert.decided_by, cert.relied_on)

    did = record(store, cert, dom.subject_type, dom.subject_key,
                 "2026-02-01T00:10:00")
    govern(store, did, artifacts)                # cite what it was checked against

    # later, from storage alone
    rc = recheck(store, did, domain=dom)
    print(rc.passed, rc.reason)
```

What each call does:

- **`sync`** recompiles the rule from its source file and compares both
  compiled forms against what is deployed. If either was edited by hand, or
  the rule changed without recompiling, it raises `Drift` and nothing runs.
- **`publish`** stores the rule source, the compiled Lean library, the
  generated types and any hand-written theorem modules in TypeDB, each by
  hash.
- **`decide`** closes the as-of window — advancing the ledger to the
  decision's date if it is behind, so no later write can be stamped inside a
  snapshot that has already been certified — then takes the snapshot, asks
  TypeDB to search, and has Lean check the result. The window is closed
  immediately before the snapshot is read, and after the subject is known
  to exist: the ledger is shared, and a decision refused for rule drift, a
  bad parameter or an unknown subject should not have moved it for
  everybody. A writer whose clock then sits behind that mark is stamped
  just past it rather than refused, so one machine's clock cannot stall the
  others — backdating is judged against the last recorded **fact**, which a
  sealed window does not move, so going behind a fact that already exists
  is still refused at any distance and no tolerance has to be tuned. `Certificate.decided_by` says how the verdict was reached:
  `witness` (TypeDB proposed facts and the kernel verified them),
  `negation` (the kernel decided the rule does **not** hold, over the whole
  snapshot), or `evaluation` (the kernel decided it without the search).
  `decide(..., suppress_search=True)` discards TypeDB's answer entirely; the
  verdict must not change.
- **`record`** writes the verdict, the proof, the snapshot hash, and
  `reliance` / `coverage` edges to the exact facts — all of it or none.
  A decision the search and the kernel disagree about is refused unless
  `allow_disagreement=True`.
- **`govern`** links the decision to the artifacts it was checked against.
- **`recheck`** re-makes the snapshot as of the decision's own date and
  confirms the hash; re-parses the rule from the **stored** rule source and
  regenerates the case file, which must match the stored one **byte for
  byte**; then rebuilds the Lean library from the artifacts stored in TypeDB
  into a fresh workspace — including its `lean-toolchain`, so the replay runs
  on the pinned Lean — and re-runs the stored proof there. It needs the
  `domain`, because it cannot re-export without one. `rc.snapshot_matches`
  and `rc.file_matches` report the first two separately, and
  `rc.kernel_recorded` / `rc.kernel_now` name the toolchain the proof was
  checked with and the one that just replayed it.

### When facts change

Facts are never edited or deleted. A correction is a dated retraction plus a
new fact, so a past snapshot still reproduces exactly.

- `decisions_relying_on(store, fact_id)` — decisions whose proof **used** that
  fact, so a retraction puts them in question.
- `affected_decisions(store, fact_id)` — decisions whose snapshot **looked
  at** the item a fact is about, which is how a fact recorded *later* finds
  the earlier decisions it would have changed. This is the half that needs
  `scope_anchors`; without it, a later fact silently leaves every earlier
  decision looking valid.
- `decisions_after_rule_change(store, ...)` — decisions taken under a
  different version of the rule.

## Tests

The tests need no TypeDB server, and nothing outside this repository: they
run against a fixture domain in `tests/fixtures/` — a neutral schema and seven
rules that between them use every construct of the rule language — whose Lean
package is generated by the core itself (`tests/fixtures/regenerate.py`).

    python3 tests/test_core.py          # the core: no server, no Lean
    python3 tests/test_bridge.py        # the type bridge's attack tests (Lean)
    python3 tests/test_lean_offline.py  # every fixture rule vs real Lean
    python3 tests/golden.py             # compiler output, pinned

`test_core.py` needs `typedb-driver` importable, though never connects. The
two Lean suites need Lean 4.35.0 (the fixture package's pin) on `PATH`;
`test_lean_offline.py` skips itself without `lake`.

- **`test_core.py`** — one check per property that was got wrong at least
  once, named after the failure it prevents: identifiers, the ledger and its
  sealed window, the type bridge, the compiler's refusals, the resolved rule
  IR, proof-term construction, kernel outcomes, polarity (property-tested
  against a reference evaluator on random snapshots), derived anchors, and
  the must-fail corpus in `tests/must_fail/`.
- **`test_lean_offline.py`** — on random snapshots of every fixture rule, the
  kernel proves the verdict the reference evaluator (`tests/refeval.py`)
  predicts and accepts the compiler's witness proof terms; a timed-out check
  comes back `not-run`.
- **`golden.py`** — what the compiler emits and what is stored from it: each
  fixture rule's Lean module (against the committed file), TypeQL search,
  shape hash and proof terms. A change here is a change to stored output, so
  it is regenerated deliberately (`regenerate.py`, then `golden.py --write`) and
  reviewed.

## What the core guarantees

1. TypeDB's schema is the only source of types, and each `.rule` file is the
   only source of its rule. Lean's types and rule, and TypeDB's search
   function, are generated from those, and verification refuses to run if
   anything in use differs.
2. Nothing generated by a language model becomes a theorem statement. The core
   builds every statement.
3. TypeDB's search is untrusted. Its witnesses are re-checked by the kernel,
   and its "nothing found" is never trusted — Lean decides absence itself.
4. The closed world is explicit. Truth is relative to a hashed, as-of
   snapshot, and ledger time only moves forward, so past snapshots never
   change.
5. Every accepted proof, and the exact rule and type artifacts it was checked
   against, is stored in TypeDB and can be re-checked from there.
6. A proof is accepted only on a clean Lean exit with no error, no `sorry`,
   and no axiom outside `propext`, `Classical.choice` and `Quot.sound`. Case
   files containing `set_option`, `native_decide`, `#eval`, `run_cmd`, `elab`,
   `macro`, `unsafe def`, `axiom` or `initialize` are refused outright,
   including stored files during `recheck`.

## What it does not promise

- That the rule matches the real policy, guideline or regulation. Experts must
  review the rule — which is why it is written in a language they can read.
- That the facts match reality. That is what sources and human confirmation
  are for.
- That nothing relevant was left out of the snapshot. The export step is kept
  deliberately simple and checks itself for dropped facts, and every
  certificate states what it covered and what it assumed.
