/-
  GENERATED from rule scoping.any-goal by attest/rulec.py. Do not edit.
  rule scoping.any-goal v0.1
  At least one goal node is marked in the shared catalog.
  rule source sha256: 01b0d946789ba4e3c13dd677f91433afcb054be078d393083ec8c3ddc823586a
-/
import Scoping.Schema

namespace Scoping.Rules.Scoping.AnyGoal
open Scoping.Schema

def ruleId : String := "scoping.any-goal v0.1"
def ruleSha256 : String := "01b0d946789ba4e3c13dd677f91433afcb054be078d393083ec8c3ddc823586a"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  goals : List GoalMark
deriving Repr

/-- At least one goal node is marked in the shared catalog. -/
def AnyGoal (s : Snapshot) : Prop :=
  ∃ g ∈ s.goals,
    g.retractedAt = none

-- Elaboration budget only. Putting the subject and the retraction
-- check on every binder grew the proposition past the default
-- instance-search size, and the search gave up on the largest
-- rule. These three options raise limits; none of them affects
-- what the kernel accepts, and `attest/rulec.py` emits no others
-- (tests/test_core.py checks that). A rule module is compared
-- byte-for-byte with a fresh compile before every decision, so it
-- cannot acquire an option the compiler did not write.
set_option synthInstance.maxSize 2000 in
instance (s : Snapshot) : Decidable (AnyGoal s) := by
  unfold AnyGoal; infer_instance

end Scoping.Rules.Scoping.AnyGoal
