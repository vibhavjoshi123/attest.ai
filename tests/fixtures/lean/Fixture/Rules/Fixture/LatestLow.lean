/-
  GENERATED from rule fixture.latest-low by attest/rulec.py. Do not edit.
  rule fixture.latest-low v0.1
  The holder's most recent alpha reading in the last 180 days is below 70.
  rule source sha256: 2272f8651ea9ad4792d6286dcfc2b93e5bb9f7289ef78d1dee99c2956bb50623
-/
import Fixture.Schema

namespace Fixture.Rules.Fixture.LatestLow
open Fixture.Schema

def ruleId : String := "fixture.latest-low v0.1"
def ruleSha256 : String := "2272f8651ea9ad4792d6286dcfc2b93e5bb9f7289ef78d1dee99c2956bb50623"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  readings : List Reading
  /-- whose case this is; every scoped binder checks it -/
  subject : String
  /-- the instant being decided, in whole days -/
  asOfDay : Int
deriving Repr

/-- The holder's most recent alpha reading in the last 180 days is below 70. -/
def LatestLow (s : Snapshot) : Prop :=
  ∃ r ∈ s.readings,
    r.holder = s.subject ∧
    r.retractedAt = none ∧
    r.testCode = .alpha ∧
    r.amount < 70 ∧
    r.takenDay ≥ (s.asOfDay - 180) ∧
    r.takenDay ≤ s.asOfDay ∧
    ¬ (∃ n ∈ s.readings,
      n.holder = s.subject ∧
      n.retractedAt = none ∧
      n.testCode = .alpha ∧
      n.factId ≠ r.factId ∧
      n.takenDay ≥ r.takenDay ∧
      n.takenDay ≤ s.asOfDay ∧
      n.amount ≠ r.amount)

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
instance (s : Snapshot) : Decidable (LatestLow s) := by
  unfold LatestLow; infer_instance

end Fixture.Rules.Fixture.LatestLow
