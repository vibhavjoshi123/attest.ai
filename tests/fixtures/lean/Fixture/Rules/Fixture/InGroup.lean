/-
  GENERATED from rule fixture.in-group by attest/rulec.py. Do not edit.
  rule fixture.in-group v0.1
  The holder has a claim whose code falls under the watched group.
  rule source sha256: 151a346660082bc63fa77d277f5d2fe6b64a5ee58ee4d8f7f27f6a873e04b7bb
-/
import Fixture.Schema

namespace Fixture.Rules.Fixture.InGroup
open Fixture.Schema

def ruleId : String := "fixture.in-group v0.1"
def ruleSha256 : String := "151a346660082bc63fa77d277f5d2fe6b64a5ee58ee4d8f7f27f6a873e04b7bb"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  claims : List Claim
  groups : List CodeIsa
  /-- whose case this is; every scoped binder checks it -/
  subject : String
deriving Repr

/-- closure `in-group` over `groups`, child → parent: one round.

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
def inGroupStep (edges : List CodeIsa) (xs : List String) : List String :=
  (xs ++ (edges.filter (fun e => e.retractedAt.isNone && xs.contains e.child)).map (·.parent)).eraseDups

/-- `x` itself and everything it reaches; `edges.length + 1` rounds reach the
    fixpoint on any finite graph, cycles included. -/
def inGroup (s : Snapshot) (x : String) : List String :=
  (List.range (s.groups.length + 1)).foldl (fun xs _ => inGroupStep s.groups xs) [x]

/-- The holder has a claim whose code falls under the watched group. -/
def InGroup (s : Snapshot) : Prop :=
  ∃ c ∈ s.claims,
    c.holder = s.subject ∧
    c.retractedAt = none ∧
    "watched" ∈ inGroup s c.code

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
instance (s : Snapshot) : Decidable (InGroup s) := by
  unfold InGroup; infer_instance

end Fixture.Rules.Fixture.InGroup
