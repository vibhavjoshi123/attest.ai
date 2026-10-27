/-
  GENERATED from rule sanctions.owned-by-listed by attest/rulec.py. Do not edit.
  rule sanctions.owned-by-listed v0.1
  A vendor is BLOCKED if it carries an ACTIVE sanctions listing itself, or is owned, directly or through a chain of owners, by a party that does.
  rule source sha256: b27624f86e1cdf3c4d4f440fcdd196578522a2ca191882a5eb58a7d1f9f519fe
-/
import Sanctions.Schema

namespace Sanctions.Rules.Sanctions.OwnedByListed
open Sanctions.Schema

def ruleId : String := "sanctions.owned-by-listed v0.1"
def ruleSha256 : String := "b27624f86e1cdf3c4d4f440fcdd196578522a2ca191882a5eb58a7d1f9f519fe"

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

/-- A vendor is BLOCKED if it carries an ACTIVE sanctions listing itself, or is owned, directly or through a chain of owners, by a party that does. -/
def Blocked (s : Snapshot) : Prop :=
  ∃ e ∈ s.engagements,
    e.vendor = s.subject ∧
    e.retractedAt = none ∧
    ∃ l ∈ s.listings,
    l.retractedAt = none ∧
    l.party ∈ ownedBy s e.vendor ∧
    l.listStatus = .active

-- Elaboration budget only. Putting the subject and the retraction
-- check on every binder grew the proposition past the default
-- instance-search size, and the search gave up on the largest
-- rule. These three options raise limits; none of them affects
-- what the kernel accepts, and `attest/rulec.py` emits no others
-- (tests/test_core.py checks that). A rule module is compared
-- byte-for-byte with a fresh compile before every decision, so it
-- cannot acquire an option the compiler did not write.
set_option synthInstance.maxSize 2000 in
instance (s : Snapshot) : Decidable (Blocked s) := by
  unfold Blocked; infer_instance

end Sanctions.Rules.Sanctions.OwnedByListed
