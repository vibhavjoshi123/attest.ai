/-
  GENERATED from rule fixture.any-listing by attest/rulec.py. Do not edit.
  rule fixture.any-listing v0.1
  At least one listing is active.
  rule source sha256: 2aae745aa675952973ee8101c9414d23b5a08f30414048da5d01b102bc17c1e7
-/
import Fixture.Schema

namespace Fixture.Rules.Fixture.AnyListing
open Fixture.Schema

def ruleId : String := "fixture.any-listing v0.1"
def ruleSha256 : String := "2aae745aa675952973ee8101c9414d23b5a08f30414048da5d01b102bc17c1e7"

/-- What one case may look at: values of the types generated from TypeDB. -/
structure Snapshot where
  listings : List Listing
deriving Repr

/-- At least one listing is active. -/
def AnyListing (s : Snapshot) : Prop :=
  ∃ l ∈ s.listings,
    l.retractedAt = none ∧
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
instance (s : Snapshot) : Decidable (AnyListing s) := by
  unfold AnyListing; infer_instance

end Fixture.Rules.Fixture.AnyListing
