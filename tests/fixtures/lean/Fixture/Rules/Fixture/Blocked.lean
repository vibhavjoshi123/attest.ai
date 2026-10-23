/-
  GENERATED from rule fixture.blocked by attest/rulec.py. Do not edit.
  rule fixture.blocked v0.1
  A holder is BLOCKED if it is engaged with a firm that has an active listing itself, or is owned, directly or through a chain of owners, by a party that does.
  rule source sha256: afbc9c4b4485529a641936ed5f11e49ec20144623bedda13d5a2f35672936bc8
-/
import Fixture.Schema

namespace Fixture.Rules.Fixture.Blocked
open Fixture.Schema

def ruleId : String := "fixture.blocked v0.1"
def ruleSha256 : String := "afbc9c4b4485529a641936ed5f11e49ec20144623bedda13d5a2f35672936bc8"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  engagements : List Engagement
  ownerships : List Ownership
  listings : List Listing
  /-- whose case this is; every scoped binder checks it -/
  subject : String
deriving Repr

/-- closure `owned-by` over `ownerships`, owned → owner: one round.

    A retracted edge is not walked. The TypeQL closure has
    always guarded this (`active($e)` on every edge); the Lean
    fold did not, because the guards were added to `some`
    binders and closure collections were left out. The two
    forms then asked different questions, and the dangerous
    direction is a walking step inside `none of`: Lean reaches
    the goal through a retracted edge, the block is false, the
    kernel decides the negation, and the search also returns
    nothing — so the per-case differential reports `agree` and
    the verdict is recorded. -/
def ownedByStep (edges : List Ownership) (xs : List String) : List String :=
  (xs ++ (edges.filter (fun e => e.retractedAt.isNone && xs.contains e.owned)).map (·.owner)).eraseDups

/-- `x` itself and everything it reaches; `edges.length + 1` rounds reach the
    fixpoint on any finite graph, cycles included. -/
def ownedBy (s : Snapshot) (x : String) : List String :=
  (List.range (s.ownerships.length + 1)).foldl (fun xs _ => ownedByStep s.ownerships xs) [x]

/-- A holder is BLOCKED if it is engaged with a firm that has an active listing itself, or is owned, directly or through a chain of owners, by a party that does. -/
def Blocked (s : Snapshot) : Prop :=
  ∃ e ∈ s.engagements,
    e.holder = s.subject ∧
    e.retractedAt = none ∧
    ∃ l ∈ s.listings,
    l.retractedAt = none ∧
    l.party ∈ ownedBy s e.counterparty ∧
    l.status = .active

-- Elaboration budget only. Putting the subject and the retraction
-- check on every binder grew the proposition past the default
-- instance-search size, and the search gave up on the largest
-- rule. These three options raise limits; none of them affects
-- what the kernel accepts, and `attest/rulec.py` emits no others
-- (the core's own test suite checks that). A rule module is
-- compared byte-for-byte with a fresh compile before every
-- decision, so it cannot acquire an option the compiler did
-- not write.
set_option synthInstance.maxSize 2000 in
instance (s : Snapshot) : Decidable (Blocked s) := by
  unfold Blocked; infer_instance

end Fixture.Rules.Fixture.Blocked
