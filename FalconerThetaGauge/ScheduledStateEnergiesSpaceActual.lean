/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.ScheduledStateEnergiesSpaceDistance
public import FalconerThetaGauge.SpaceSplittingEnergy

/-! # The complete actual space-splitting move for the genuine finite scheduled states -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

set_option maxHeartbeats 800000 in
theorem actualSpaceSplittingRecurrence (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    ActualSpaceSplittingRecurrence ρ θ N := by
  intro i hi b e a v hs hlong hsmall
  let A := regularMeasureExcess ρ N
  let q := blockCount θ N
  let I := profileRemainingTests A q N b e a
  let L := profileLongestTestLength A q N b e a
  let p := profileNearStart A q N (toleranceCount θ N) b e a v
  have hN : 0 < N := by have := hpar.1; omega
  have hq := blockCount_pos θ hN
  have hlevels : 0 < maskLevelCount θ N := by unfold maskLevelCount; omega
  have hgeo := regularProfileNearStart_source_geometry (ρ := ρ) hpar hs hlong hsmall
  change a < p ∧ p ≤ v ∧ p ≤ N ∧ p + 12 ≤ v + 1 ∧
    min (v + 1) (p + 12) = p + 12 ∧
      2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - p at hgeo
  have hcard : I.card ≤ N ^ 2 + 1 := regularRemainingTests_card_le hpar hs.2.2.2.1
  have hL : L ≤ N := profileLongestTestLength_le_terminal hq hs.2.2.2.1
  have hlength : ∀ test ∈ I, test.length ≤ L := fun _ ht ↦
    profileRemainingTests_length_le_longest ht
  have hv : v ≤ N := hs.2.2.1.trans hs.2.2.2.1
  change regularMeasureStateEnergy ρ θ N i (.fourier b e a v) ≤
    81 ^ 2 * regularMeasureStateEnergy ρ θ N i (.fourier b e p v) +
      (2 : ℝ) ^ (90 : ℝ) * ∑ n ∈ Finset.Ioo a (min (v + 1) (p + 12)),
        regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy n v) +
      (2 : ℝ) ^ (-(25 * (N : ℝ)))
  rw [hgeo.2.2.2.2.1]
  change profileFourierStateEnergy ρ A q N (tolerance θ N * N)
    (maskLevelCount θ N) i (8 * expansionCount θ N) (2 * expansionCount θ N)
    (8 * expansionCount θ N) b e a v ≤ _
  apply finiteEnergyMaximum_le _ _ (by
    have hnear := regularMeasureStateEnergy_nonneg ρ θ N i (.fourier b e p v)
    have hfar : 0 ≤ ∑ n ∈ Finset.Ioo a (p + 12),
        regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy n v) :=
      sum_nonneg (fun _ _ ↦ regularMeasureStateEnergy_nonneg ..)
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) hnear)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hfar))
        (Real.rpow_nonneg (by norm_num) _))
  intro P hP
  obtain ⟨hX, hY⟩ := mem_product.1 hP
  apply csSup_le (scheduledFourierEnergyValues_nonempty ..)
  rintro z ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  have hcell := maskedFourierEnergy_spaceSplitting_le_source ρ hρ hpar hlevels
    hpar.directional_level_size i I hcard (profileRemainingTests_ordered A hq hs.2.2.2.1)
    hL hlength hgeo.1.le hgeo.2.2.1 hv hgeo.2.2.2.2.2 P.1 P.2 hb₁ hb₂
  have hnear := sum_maskedFourierEnergy_remaining_le_refined_state ρ A q N
    (tolerance θ N * N) (maskLevelCount θ N) i (8 * expansionCount θ N) (by omega)
    (8 * expansionCount θ N) b e hgeo.1.le v hX hY hb₁ hb₂
  change spaceSplittingFineEnergyAverage ρ a p P.1 P.2 b₁ b₂
    (8 * expansionCount θ N) v ≤ regularMeasureStateEnergy ρ θ N i
      (.fourier b e p v) at hnear
  have hfar :
      (∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDistanceMaximum ρ a n P.1 P.2
        (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
          (directionalLevelWidth (maskLevelCount θ N) (i + 1)) I I) v) ≤
      ∑ n ∈ Finset.Ioo a (p + 12),
        regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy n v) := by
    apply sum_le_sum
    intro n hn
    exact regularRemainingDistanceMaximum_le_far_child ρ θ hN hs.1 (mem_Ioo.1 hn).1
      hs.2.2.1 hs.2.2.2.1 P.1 P.2 i
  have hh := hcell.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hnear (by positivity))
      (mul_le_mul_of_nonneg_left hfar (by positivity))) le_rfl)
  have h90 : (2 : ℝ) ^ (90 : ℝ) = (2 : ℝ) ^ (90 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (2 : ℝ) (90 : ℕ)
  rw [h90]
  simpa only [neg_mul] using hh

end FalconerThetaGauge
