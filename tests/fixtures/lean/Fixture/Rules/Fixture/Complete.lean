/-
  GENERATED from rule fixture.complete by attest/rulec.py. Do not edit.
  rule fixture.complete v0.1
  The item is complete for the holder when every criterion of the item has a met resolution for the holder.
  rule source sha256: 791e143cf13ba4073c4e642f42f16e59498b0e5f4f526f6aa9bc7254f9964b42
-/
import Fixture.Schema

namespace Fixture.Rules.Fixture.Complete
open Fixture.Schema

def ruleId : String := "fixture.complete v0.1"
def ruleSha256 : String := "791e143cf13ba4073c4e642f42f16e59498b0e5f4f526f6aa9bc7254f9964b42"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  marks : List ItemMark
  crits : List Criterion
  resols : List Resolution
  /-- whose case this is; every scoped binder checks it -/
  subject : String
  /-- input `target`: the key of the item decided about -/
  target : String
deriving Repr

/-- The item is complete for the holder when every criterion of the item has a met resolution for the holder. -/
def Complete (s : Snapshot) : Prop :=
  ∃ m ∈ s.marks,
    m.item = s.target ∧
    m.retractedAt = none ∧
    ¬ (∃ c ∈ s.crits,
      c.item = s.target ∧
      c.retractedAt = none ∧
      ¬ (∃ v ∈ s.resols,
        v.holder = s.subject ∧
        v.retractedAt = none ∧
        v.critKey = c.critKey ∧
        v.state = .met))

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
instance (s : Snapshot) : Decidable (Complete s) := by
  unfold Complete; infer_instance

end Fixture.Rules.Fixture.Complete
