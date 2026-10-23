/-
  GENERATED from rule fixture.two-parties by attest/rulec.py. Do not edit.
  rule fixture.two-parties v0.1
  The holder is engaged with at least two different counterparties.
  rule source sha256: 838972eb477416f640696fea532a886696a67e15602f92b5c5be50f053675da8
-/
import Fixture.Schema

namespace Fixture.Rules.Fixture.TwoParties
open Fixture.Schema

def ruleId : String := "fixture.two-parties v0.1"
def ruleSha256 : String := "838972eb477416f640696fea532a886696a67e15602f92b5c5be50f053675da8"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  engagements : List Engagement
  /-- whose case this is; every scoped binder checks it -/
  subject : String
deriving Repr

/-- The holder is engaged with at least two different counterparties. -/
def TwoParties (s : Snapshot) : Prop :=
  ∃ a ∈ s.engagements,
    a.holder = s.subject ∧
    a.retractedAt = none ∧
    ∃ b ∈ s.engagements,
    b.holder = s.subject ∧
    b.retractedAt = none ∧
    a.counterparty ≠ b.counterparty

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
instance (s : Snapshot) : Decidable (TwoParties s) := by
  unfold TwoParties; infer_instance

end Fixture.Rules.Fixture.TwoParties
