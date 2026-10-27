import Fixture.Rules.Fixture.LatestHigh
import Fixture.Rules.Fixture.LatestLow
open Fixture.Schema
open Fixture.Rules.Fixture.LatestHigh (LatestHigh)
open Fixture.Rules.Fixture.LatestLow (LatestLow)

/- Properties OF the alpha-band rules, checked by the kernel.

   Claims about the RULES, quantified over snapshots — not about any one
   holder, which is why no amount of per-holder testing finds them. Each
   theorem pins shut a defect the band's historical rules had; the mutants in
   tests/mutants/fixture/ reproduce them, and the counterexample search finds
   them unaided. Hand-written: `tests/fixtures/regenerate.py` writes the rule
   modules and the root, never this file. -/

namespace Fixture.Properties

/-- Two alpha readings taken on the SAME day, 68 and 78, both this holder's
    and neither retracted. -/
def low : Reading :=
  { holder := "h-x", takenDay := 900, factId := "r-low",
    recordedAt := "2026-01-01T00:00:00", retractedAt := none,
    source := "feed:x", testCode := .alpha, amount := 68 }

def high : Reading := { low with factId := "r-high", amount := 78 }

/-- **Defect 1.** "Latest" was "no alpha reading with a strictly greater
    taken-day". Two readings sharing a day were each not-older-than the
    other, so both qualified and the holder was in both branches at once,
    each with a valid proof. A genuine conflict now picks no branch. -/
theorem conflicting_same_day_readings_pick_no_branch :
    ¬ LatestHigh ⟨[low, high], "h-x", 1000⟩ ∧
    ¬ LatestLow ⟨[low, high], "h-x", 1000⟩ := by decide

/-- **Defect 2, the first fix for defect 1.** Keying the tie-break on
    `fact-id` alone silenced the branch for *any* two records sharing the
    newest day — including two IDENTICAL readings from two feeds, where
    nothing conflicts. -/
theorem duplicate_readings_still_decide :
    LatestHigh ⟨[high, {high with factId := "r-high-dup"}],
                "h-x", 1000⟩ := by decide

/-- **Defect 3.** A window bounded only below let a reading dated after the
    decision satisfy recency *and* win "latest". The bound has to be inside
    the `none of` too, or a future record still blocks the real one. -/
theorem future_dated_reading_is_ignored :
    LatestHigh ⟨[high, {low with factId := "r-future", takenDay := 1100}],
                "h-x", 1000⟩ := by decide

/-- **Scope and retraction.** A retracted reading, or one belonging to a
    different holder, proves nothing. -/
theorem a_foreign_retracted_reading_proves_nothing :
    ¬ LatestHigh ⟨[{high with holder := "h-SOMEONE-ELSE"}], "h-x", 1000⟩ ∧
    ¬ LatestHigh ⟨[{high with retractedAt := some "2026-02-01T00:00:00"}],
                  "h-x", 1000⟩ := by decide

/-- And the ordinary cases still work: one clear reading decides, and the
    newer of two on different days wins. -/
theorem the_rules_still_decide :
    (LatestHigh ⟨[high], "h-x", 1000⟩ ∧
     ¬ LatestLow ⟨[high], "h-x", 1000⟩) ∧
    (LatestLow ⟨[{high with takenDay := 800}, low], "h-x", 1000⟩ ∧
     ¬ LatestHigh ⟨[{high with takenDay := 800}, low], "h-x", 1000⟩) := by
  decide

/-- **Exclusivity, over every snapshot.** Not `by decide`: this quantifies
    over all snapshots, so it is a proof rather than an evaluation, and it is
    the form a `family … exclusive:` declaration would generate. The fact-id
    hypothesis is enforced at the boundary by `attest.make_snapshot`, and is
    stated here because the Lean type cannot express it. -/
theorem band_exclusive
    (readings : List Reading) (subject : String) (day : Int)
    (ids : ∀ x ∈ readings, ∀ y ∈ readings, x.factId = y.factId → x = y) :
    ¬ (LatestHigh ⟨readings, subject, day⟩ ∧
       LatestLow ⟨readings, subject, day⟩) := by
  rintro ⟨⟨a, ha, hasub, haret, hac, hav, _, hahi, hamax⟩,
          ⟨b, hb, hbsub, hbret, hbc, hbv, _, hbhi, hbmax⟩⟩
  have hvne : b.amount ≠ a.amount := by omega
  have hid : a.factId ≠ b.factId := by
    intro h
    have hab : a = b := ids a ha b hb h
    rw [hab] at hav
    omega
  have h1 : ¬ (b.takenDay ≥ a.takenDay) := fun hge =>
    hamax ⟨b, hb, hbsub, hbret, hbc, Ne.symm hid, hge, hbhi, hvne⟩
  have h2 : ¬ (a.takenDay ≥ b.takenDay) := fun hge =>
    hbmax ⟨a, ha, hasub, haret, hac, hid, hge, hahi, Ne.symm hvne⟩
  omega

/-- A holder whose only alpha reading (81) is 200 days old matches NEITHER
    branch, and neither does a holder with no alpha reading at all. -/
def stale : Reading :=
  { holder := "h-x", takenDay := 800, factId := "r-x",
    recordedAt := "2026-01-01T00:00:00", retractedAt := none,
    source := "feed:x", testCode := .alpha, amount := 81 }

theorem stale_reading_matches_no_branch :
    ¬ LatestHigh ⟨[stale], "h-x", 1000⟩ ∧
    ¬ LatestLow ⟨[stale], "h-x", 1000⟩ := by decide

theorem no_reading_matches_no_branch :
    ¬ LatestHigh ⟨[], "h-x", 1000⟩ ∧
    ¬ LatestLow ⟨[], "h-x", 1000⟩ := by decide

end Fixture.Properties

#print axioms Fixture.Properties.conflicting_same_day_readings_pick_no_branch
#print axioms Fixture.Properties.duplicate_readings_still_decide
#print axioms Fixture.Properties.future_dated_reading_is_ignored
#print axioms Fixture.Properties.a_foreign_retracted_reading_proves_nothing
#print axioms Fixture.Properties.the_rules_still_decide
#print axioms Fixture.Properties.band_exclusive
#print axioms Fixture.Properties.stale_reading_matches_no_branch
#print axioms Fixture.Properties.no_reading_matches_no_branch
