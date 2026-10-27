/-
  GENERATED from rule scoping.reaches by attest/rulec.py. Do not edit.
  rule scoping.reaches v0.1
  The goal node is reachable from the sample's start node over edges the sample has opened.
  rule source sha256: 2f15d41c6fd69b5d10c02dc2e4ecdde677afe9c34fac3389b39a756c8502849b
-/
import Scoping.Schema

namespace Scoping.Rules.Scoping.Reaches
open Scoping.Schema

def ruleId : String := "scoping.reaches v0.1"
def ruleSha256 : String := "2f15d41c6fd69b5d10c02dc2e4ecdde677afe9c34fac3389b39a756c8502849b"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  starts : List StartNode
  goals : List GoalMark
  edges : List OpenEdge
  /-- whose case this is; every scoped binder checks it -/
  subject : String
  /-- input `goal`: the key of the node decided about -/
  goal : String
deriving Repr

/-- closure `reach` over `edges` (scoped to `subject`), origin → target: one round.
    Only unretracted edges belonging to the scope are walked. -/
def reachStep (sc : String) (edges : List OpenEdge) (xs : List String) : List String :=
  (xs ++ (edges.filter (fun e => e.retractedAt.isNone && e.sample == sc && xs.contains e.origin)).map (·.target)).eraseDups

/-- `x` itself and everything it reaches within the scope. -/
def reach (s : Snapshot) (x : String) : List String :=
  (List.range (s.edges.length + 1)).foldl (fun xs _ => reachStep s.subject s.edges xs) [x]

/-- The goal node is reachable from the sample's start node over edges the sample has opened. -/
def Reaches (s : Snapshot) : Prop :=
  ∃ a ∈ s.starts,
    a.sample = s.subject ∧
    a.retractedAt = none ∧
    ∃ g ∈ s.goals,
    g.node = s.goal ∧
    g.retractedAt = none ∧
    g.node ∈ reach s a.node

-- Elaboration budget only. Putting the subject and the retraction
-- check on every binder grew the proposition past the default
-- instance-search size, and the search gave up on the largest
-- rule. These three options raise limits; none of them affects
-- what the kernel accepts, and `attest/rulec.py` emits no others
-- (tests/test_core.py checks that). A rule module is compared
-- byte-for-byte with a fresh compile before every decision, so it
-- cannot acquire an option the compiler did not write.
set_option synthInstance.maxSize 2000 in
instance (s : Snapshot) : Decidable (Reaches s) := by
  unfold Reaches; infer_instance

end Scoping.Rules.Scoping.Reaches
