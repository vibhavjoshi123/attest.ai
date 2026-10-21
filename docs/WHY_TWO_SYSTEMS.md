# Why two systems: TypeDB and Lean, from the inside

```
<name>.rule ──┬──> a Lean definition    the authority: what gets proved
              └──> a TypeQL function    fast, untrusted: finds candidates
```

Attest compiles every rule into two programs that run on two very different
machines. This document explains why, in terms of what the two systems
actually do internally. It summarises a set of source-level deep-dives into
TypeDB 3 (`typedb/typedb`, `typeql`, `typedb-driver`, `typedb-protocol`,
`typedb-behaviour`) and Lean 4 (`leanprover/lean4`), read at their default
branches.

---

## 1. Finding and checking are different problems

To decide that a rule **holds**, someone has to *find* the handful of facts
that line up to satisfy it — possibly through a chain of reference data —
among millions. To be sure of that answer, someone has to *check* that what
was found really does satisfy the rule.

Finding is a search problem: indexes, join orders, statistics, recursion.
Checking is a verification problem: a small, auditable procedure that accepts
only what follows from the definitions. This is the asymmetry of an NP
certificate — finding is hard, checking a found answer is easy.

TypeDB is engineered for the first. Lean's kernel is engineered for the
second. Neither can do the other's job well, and the source shows why.

## 2. TypeDB is a search engine for typed facts

- **Built for traversal at scale.** Data lives in five RocksDB instances,
  with index entries in both directions for role players and ownership. That
  makes "every relation whose given role is played by X" and "every relation
  X plays in" single prefix scans. Planner statistics are kept, and recovered
  from TypeDB's own write-ahead log.
- **A real optimiser.** Queries are parsed (pest grammar), translated to an
  IR, and type-annotated. Every variable gets a set of possible types, which
  are seeded, propagated and pruned — this is where `INF11` comes from. A
  beam-search planner over a cost model then orders the joins, and a
  pull-based, depth-first executor streams rows in batches of 64.
- **Recursion by tabling.** A recursive function gets an answer table per
  `(function, arguments)`, with duplicates removed. Calls that run ahead of
  their own results are suspended and resumed until no table grows. A
  **stratification check (`FUN9`)** forbids recursion through negation,
  reductions or single-value returns, so a recursive rule always has one
  well-defined result.
- **A transaction is one bidirectional gRPC stream.** Requests are batched
  every 50 µs, and answers are prefetched, 32 at a time by default, with
  back-pressure from the client. Driver and server agree only on a protocol
  version, not on product versions. Errors reach Python as message text, so
  codes like `[CNT5]` are matched in the message, and a commit reports only
  the first violation.
- **Types reject nonsense before it is stored.** `@values` (`CNT8`) and
  `@key`/`@unique` (`CNT9`) fail while the write query runs. `@card` (`CNT5`)
  fails at commit, before the write-ahead log is touched. Functions are
  type-checked and stratification-checked when the schema commits.

**What TypeDB does not give** (and why it cannot be the authority):

- **Answers are rows, not evidence.** Nothing records *why* a row is in the
  result, and no small checker could re-verify it.
- **The trusted base is the whole engine:** parser, type inference, planner,
  executor, tabling, storage and isolation. The source has known weak spots.
  Function type checking runs two rounds rather than to convergence (a TODO
  the authors flag themselves). A recursive call is costed with a fixed
  placeholder. And isolation is weaker than snapshot isolation: TypeDB's own
  tests document **lost updates and write skew**.
- **No termination guarantee.** There is no termination check and no depth
  limit for recursive functions; only the transaction timeout stops a
  runaway.
- **Bag semantics.** An untabled function returns a bag, and multiplicity is
  invisible to the driver.
- **No supported "as-of" reads.** The engine can open a snapshot at an old
  commit number, but no driver exposes it, commit numbers are not times, and
  old versions are not protected from cleanup. Attest therefore keeps its own
  `recorded-at` / `retracted-at` ledger rather than relying on storage
  versions.

## 3. Lean's kernel is a small checker

- **One small door.** About 5,400 lines of C++, reached only through
  `lean_add_decl`. Everything else is outside the trusted base: the parser,
  the elaborator and its unifier, type-class resolution, tactics, `simp`, the
  compiler, Lake. Whatever they produce is re-checked.
- **Checking a `decide` proof is one equality.** `by decide` elaborates to
  `of_decide_eq_true (Eq.refl true)`. The kernel's job is to confirm
  `decide p` reduces to `true`, by running the `Decidable` instance inside
  its own weak-head normaliser. The elaborator has already evaluated it once,
  untrusted, so it is evaluated twice.
- **What reduction costs.** Natural-number arithmetic is accelerated with
  GMP. Strings are not: comparing two strings that are not both literals
  expands them to constructors and compares them character by character.
- **Axioms are explicit.** `#print axioms` lists every axiom a theorem
  depends on. Attest accepts only `propext`, `Classical.choice` and
  `Quot.sound`. That rejects `native_decide` in both its older form
  (`Lean.ofReduceBool`, where the kernel itself ran compiled code) and its
  newer form (a fresh axiom per use).

**What Lean does not give:**

- **It does not store or search data at scale.** A case's facts must arrive
  as a term.
- **Exhaustive checks are expensive.** Measured on a representative rule with
  two existential witnesses and one recursive closure, proving the negation
  by `decide` took roughly 0.5 s for 8 facts, 2.3 s for 16 and 14 s for 32.
  At 32, plain `decide` hit the elaborator's recursion limit while
  `decide +kernel` succeeded.
- **Imports are trusted as built.** Imported `.olean` files are not
  re-checked. `#print axioms` is a dependency walk outside the kernel, which
  code run during elaboration in the same process can deceive; core's own
  tests show this. End-to-end assurance needs the environment replayed
  through a kernel, using `leanchecker` or an independent checker.

## 4. The asymmetry that makes the pair work

| | TypeDB (search) | Lean kernel (check) |
|---|---|---|
| Scale | millions of facts, indexed | one case's snapshot (tens to hundreds of facts) |
| Output | rows (fact-ids) | a theorem, or a rejection |
| Trusted base | the whole engine | ~5.4k lines of C++ (+ allow-listed axioms) |
| Recursion | tabling, stratified, no termination check | structural (`List.range` bound), always terminates |
| Cost of *holds* | one search | **cheap**: checks the witness's ground facts |
| Cost of *does not hold* | "nothing found" (untrusted) | **expensive**: exhaustive over the snapshot |

The pairing exploits that asymmetry:

- **The rule holds:** TypeDB finds the facts, and Lean checks a proof built
  from exactly those records. The check is cheap, because the hard part —
  finding — was done by the fast, untrusted system.
- **The rule does not hold:** TypeDB's "nothing found" is never trusted,
  because a bug, a planner error or an isolation anomaly would all look like
  an honest empty answer. Lean decides absence itself, over a snapshot kept
  small enough to decide.

The single `.rule` source keeps the two programs answering the same question.
A per-case agreement check catches the remaining risk, a compiler bug: a
missed conflict shows up as `DISAGREE`.

## 5. One rule, traced through both machines

**In TypeDB.**

1. At `sync`, the compiled `define` is stored as source text. It is
   type-annotated and stratification-checked when the schema commits. An
   abstract supertype stays abstract inside the function body, and its
   subtypes all satisfy it.
2. When the witness function is called, the planner orders the subject's
   scoped collections and any `let $c in <closure>(…)` calls.
3. A closure function is tabled. Its recursive call keeps the same arguments,
   so it reaches a fixpoint on any finite graph, cycles included.
4. The `not { … }` checks for retraction stop at their first match. Rows
   stream back as fact-ids.

**In Lean.**

1. The case file's `snap` literal is elaborated against the generated
   structures.
2. The witness proof `⟨rec, by decide, …⟩` is elaborated against the expected
   type. The conclusion is unfolded to nested `Exists`/`And`, and the extra
   arguments of the anonymous constructor flatten into them.
3. Each `by decide` runs after the witnesses are fixed.
4. `addDecl` sends the finished term to the kernel, which re-evaluates every
   `decide` while checking `Eq.refl true`.
5. `#print axioms` reports `[propext]`, which enters through `List`
   membership lemmas, in proofs only.

## 6. What reading the source changed in the core

| Finding | Fix |
|---|---|
| A rejected declaration is re-added as an **axiom with the same name**, and elaboration errors become `sorry` | A proof is accepted only with exit code 0, no error, no `sorry`, and allow-listed axioms |
| `set_option debug.skipKernelTC true` **skips the kernel**, and code run during elaboration can deceive `#print axioms` | `kernel.forbidden`: case files containing `set_option`, `#eval`, `run_cmd`/`run_tac`/`run_elab`, `elab`, `macro`, `syntax`, `implemented_by`, `@[extern`, `native_decide`, `unsafe def`, `axiom` or `initialize` are refused — including stored files during `recheck` |
| Strings written with JSON escaping turn characters outside the Basic Multilingual Plane into **surrogates that Lean reads as `'\0'`**, so two distinct names could collide | `typebridge.lean_str` writes Lean string literals directly |
| No **pinned toolchain** | Each Lake package pins its own toolchain in `lean-toolchain`, and every certificate records the `lean --version` that checked it |
| A zero-row match-insert reports **no error** | `must_affect` rolls back the whole write |
| After a failed write query, the transaction either **keeps its partial writes** (the storage layer's reading) or **is killed and loses its earlier inserts** (the server's reading) | Safe under either reading: `Store.write` never commits after an error. An exception exits the transaction without committing, and `must_affect` rolls back explicitly |
| No supported as-of reads, and commit numbers are not times | The core keeps its own `recorded-at` / `retracted-at` ledger |

## 7. What remains, and the path forward

- **Independent kernel replay.** Lean v4.35 ships `leanchecker` (replays the
  environment through the kernel) and `lake comparator` (checks in a sandbox
  that a proof proves the *intended* statement). Either could replace the
  in-process `#print axioms` check with one that does not trust the same
  process that produced the proof. `recheck` already rebuilds the Lean
  library from the artifacts stored in TypeDB, in a fresh workspace, so the
  kernel re-checks every module; running `leanchecker` on that workspace
  would close the remaining gap.
- **Scale the negative direction.** Exhaustive `decide` grows quickly with
  snapshot size. The scalable pattern, used by `omega` and `grind`, is a
  checker written and **proved correct in Lean once**, after which each case
  is a cheap `Bool` evaluation with no extra axioms. Mapping names to `Nat`
  ids also helps, since the kernel accelerates `Nat` but not strings.
  `bv_decide` does not fit: its proofs carry a non-standard axiom.
- **TypeDB production settings.** The server defaults to an `admin` /
  `password` user and has no per-database permissions. Its auth tokens are
  signed with a key regenerated at every restart, and usage reporting is on
  by default. Production needs changed credentials, TLS (`TYPEDB_TLS=1`), and
  reporting turned off (`--diagnostics.reporting.metrics false`).
- **Witnesses are sets.** TypeDB's behaviour specs guarantee only
  set-equivalent results, so the core compares witnesses as sets and picks a
  deterministic one.
- **TypeDB concurrency.** Because isolation allows lost updates and write
  skew, keep fact ingestion to a single writer, or serialise writes per
  subject, and retry on lock conflicts (`STC2`).

## 8. Versions these readings describe

Lean v4.35.0 and TypeDB 3.12+ with `typedb-driver` 3.13.6. The driver and the
server must agree on the network protocol version: driver 3.8.0 implements
protocol 7.1, and a 3.12 server requires 8.2, so an older driver is refused
at connect time. `attest/store.py` detects the `DriverOptions` constructor
change between those two driver generations by capability, not by version
string, so it works with either.
