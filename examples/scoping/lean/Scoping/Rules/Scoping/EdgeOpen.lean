/-
  GENERATED from rule scoping.edge-open by attest/rulec.py. Do not edit.
  rule scoping.edge-open v0.1
  The edge is open for the sample when every criterion of the edge has a resolved-true resolution for the sample.
  rule source sha256: 0eb489677842ecb3f2a0b39bc18efbd0240058a97a0ba960890bde5b89a9f418
-/
import Scoping.Schema

namespace Scoping.Rules.Scoping.EdgeOpen
open Scoping.Schema

def ruleId : String := "scoping.edge-open v0.1"
def ruleSha256 : String := "0eb489677842ecb3f2a0b39bc18efbd0240058a97a0ba960890bde5b89a9f418"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  marks : List EdgeMark
  crits : List Criterion
  resols : List Resolution
  /-- whose case this is; every scoped binder checks it -/
  subject : String
  /-- input `edge`: the key of the edge-def decided about -/
  edge : String
deriving Repr

/-- The edge is open for the sample when every criterion of the edge has a resolved-true resolution for the sample. -/
def EdgeOpen (s : Snapshot) : Prop :=
  ∃ m ∈ s.marks,
    m.edge = s.edge ∧
    m.retractedAt = none ∧
    ¬ (∃ c ∈ s.crits,
      c.edge = s.edge ∧
      c.retractedAt = none ∧
      ¬ (∃ v ∈ s.resols,
        v.sample = s.subject ∧
        v.retractedAt = none ∧
        v.critKey = c.critKey ∧
        v.state = .resolved_true))

-- Elaboration budget only. Putting the subject and the retraction
-- check on every binder grew the proposition past the default
-- instance-search size, and the search gave up on the largest
-- rule. These three options raise limits; none of them affects
-- what the kernel accepts, and `attest/rulec.py` emits no others
-- (tests/test_core.py checks that). A rule module is compared
-- byte-for-byte with a fresh compile before every decision, so it
-- cannot acquire an option the compiler did not write.
set_option synthInstance.maxSize 2000 in
instance (s : Snapshot) : Decidable (EdgeOpen s) := by
  unfold EdgeOpen; infer_instance

end Scoping.Rules.Scoping.EdgeOpen
