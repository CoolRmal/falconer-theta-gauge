/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryShellNumbers

/-!
# The actual lists used for each regular piece

The list adds the entry tube `[0,c]` to the concrete list of `[c,N]`. It has
at most `N²+1` tests, all remaining scheduled anchors lie strictly above `c`,
and restricting the list to such anchors drops precisely the entry tube.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- Every scheduled test is anchored strictly inside its parent interval. -/
theorem profileScheduledTests_anchor_strict {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profileScheduledTests A q N a t) : a < test.anchor := by
  obtain ⟨a', t', ha', ht', hlong, hanchor, _⟩ := profileScheduledTests_origin hq ht htest
  have hp := profileSplitPoint_bounds (A := A) hq (ht'.trans ht) hlong
  rw [hanchor]
  omega

/-- The concrete list of a piece with entry depth `c`. -/
def profilePieceTests (A : ℕ → ℝ) (q N c : ℕ) : Finset ProfileScheduleTest :=
  {⟨.tube, c, 0⟩} ∪ profileScheduledTests A q N c N

/-- The actual list of a regular measure with its constructed entry depth. -/
def regularMeasurePieceTests (ρ : MeasureTheory.Measure Plane) (θ : ℝ) (N : ℕ) :
    Finset ProfileScheduleTest :=
  profilePieceTests (regularMeasureExcess ρ N) (blockCount θ N) N
    (regularMeasureEntryDepth ρ θ N)

theorem profilePieceTests_card_le_scale_sq_add_one (A : ℕ → ℝ) {θ : ℝ} {N c : ℕ}
    (hpar : ParameterFacts θ N) :
    (profilePieceTests A (blockCount θ N) N c).card ≤ N ^ 2 + 1 := by
  have hcard := profileScheduledTests_card_le_scale_sq A (a := c) hpar (le_refl N)
  have hunion := Finset.card_union_le ({⟨.tube, c, 0⟩} : Finset ProfileScheduleTest)
    (profileScheduledTests A (blockCount θ N) N c N)
  simp only [Finset.card_singleton] at hunion
  exact hunion.trans (by omega)

/-- Reaching the entry depth drops its tube and retains exactly the scheduled list. -/
theorem profilePieceTests_filter_after_entry (A : ℕ → ℝ) {q N c : ℕ} (hq : 0 < q) :
    (profilePieceTests A q N c).filter (fun test ↦ c < test.anchor) =
      profileScheduledTests A q N c N := by
  ext test
  simp only [Finset.mem_filter, profilePieceTests, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro ⟨htest, hanchor⟩
    rcases htest with rfl | htest
    · simp only at hanchor
      omega
    · exact htest
  · intro htest
    exact ⟨Or.inr htest, profileScheduledTests_anchor_strict hq (le_refl N) htest⟩

/-- The actual lists satisfy the root-shell length condition in Proposition 9.3. -/
theorem profilePieceTests_root_lengths {A : ℕ → ℝ} {q N c : ℕ}
    (hq : 0 < q) (hc : 2 * c ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profilePieceTests A q N c) :
    2 * test.length ≤ N ∧ test.length ≤ N - c := by
  rcases Finset.mem_union.mp htest with hentry | hscheduled
  · have heq : test = ⟨.tube, c, 0⟩ := Finset.mem_singleton.mp hentry
    subst test
    change 2 * (c - 0) ≤ N ∧ c - 0 ≤ N - c
    omega
  · have hlength := profileScheduledTests_length_bounds hq (le_refl N) hscheduled
    omega

/-- A concrete injective padding slot for every actual piece test. -/
def profilePieceTestEmbedding (A : ℕ → ℝ) {θ : ℝ} {N c : ℕ}
    (hpar : ParameterFacts θ N) :
    {test // test ∈ profilePieceTests A (blockCount θ N) N c} ↪ Fin (N ^ 2 + 1) :=
  (Fintype.equivFin {test // test ∈ profilePieceTests A (blockCount θ N) N c}).toEmbedding.trans
    (Fin.castLEEmb (by
      simpa only [Fintype.card_coe] using profilePieceTests_card_le_scale_sq_add_one A hpar))

end FalconerThetaGauge
