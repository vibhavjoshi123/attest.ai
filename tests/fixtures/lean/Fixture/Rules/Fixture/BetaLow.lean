/-
  GENERATED from rule fixture.beta-low by attest/rulec.py. Do not edit.
  rule fixture.beta-low v0.1
  The holder's most recent beta reading in the last 365 days is below 300.
  rule source sha256: 1c14a2245e783a89d972161cfc9cb2b15d8e9bc29c0ec331f6225d151bd8f055
-/
import Fixture.Schema

namespace Fixture.Rules.Fixture.BetaLow
open Fixture.Schema

def ruleId : String := "fixture.beta-low v0.1"
def ruleSha256 : String := "1c14a2245e783a89d972161cfc9cb2b15d8e9bc29c0ec331f6225d151bd8f055"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  readings : List Reading
  /-- whose case this is; every scoped binder checks it -/
  subject : String
  /-- the instant being decided, in whole days -/
  asOfDay : Int
deriving Repr

/-- The holder's most recent beta reading in the last 365 days is below 300. -/
def BetaLow (s : Snapshot) : Prop :=
  ∃ e ∈ s.readings,
    e.holder = s.subject ∧
    e.retractedAt = none ∧
    e.testCode = .beta ∧
    e.amount < 300 ∧
    e.takenDay ≥ (s.asOfDay - 365) ∧
    e.takenDay ≤ s.asOfDay ∧
    ¬ (∃ n ∈ s.readings,
      n.holder = s.subject ∧
      n.retractedAt = none ∧
      n.testCode = .beta ∧
      n.factId ≠ e.factId ∧
      n.takenDay ≥ e.takenDay ∧
      n.takenDay ≤ s.asOfDay ∧
      n.amount ≠ e.amount)

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
instance (s : Snapshot) : Decidable (BetaLow s) := by
  unfold BetaLow; infer_instance

end Fixture.Rules.Fixture.BetaLow
