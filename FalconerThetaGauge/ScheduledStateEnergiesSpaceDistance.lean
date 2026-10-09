/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.ScheduledStateEnergiesSpaceGeometry
public import FalconerThetaGauge.SpaceSplittingIntegratedKernel

/-! # Every literal far distance maximum is controlled by the genuine scheduled child state -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem regularRemainingDistanceMaximum_le_far_child (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (θ : ℝ) {N b e a n v : ℕ} (hN : 0 < N)
    (hba : b ≤ a) (han : a < n) (hve : v ≤ e) (he : e ≤ N)
    (X Y : Fin 2 → ℤ) (i : ℕ) :
    spaceSplittingDistanceMaximum ρ a n X Y
      (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
        (directionalLevelWidth (maskLevelCount θ N) (i + 1))
        (profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a)
        (profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a)) v ≤
      regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy n v) := by
  unfold spaceSplittingDistanceMaximum
  apply finiteEnergyMaximum_le _ _ (regularMeasureStateEnergy_nonneg ..)
  intro P hP
  have hpair : P.1 ∈ occupiedUnitCells ρ n ∧ P.2 ∈ occupiedUnitCells ρ n ∧
      SeparatedDyadicCells n P.1 P.2 := by
    have hh (A : Fin 2 → ℤ) (hh : P ∈ spaceSplittingSeparatedPairs ρ a n A) :
        P.1 ∈ occupiedUnitCells ρ n ∧ P.2 ∈ occupiedUnitCells ρ n ∧
          SeparatedDyadicCells n P.1 P.2 := by
      obtain ⟨hdesc, hsep⟩ := mem_filter.1 hh
      obtain ⟨h₁, h₂⟩ := mem_product.1 hdesc
      exact ⟨occupiedCellDescendant_mem_occupied ρ h₁,
        occupiedCellDescendant_mem_occupied ρ h₂, hsep⟩
    rcases mem_union.1 hP with hX | hY
    · exact hh X hX
    · exact hh Y hY
  exact regularRemainingDistanceEnergy_le_far_child ρ θ hN hba han hve he i
    hpair.1 hpair.2.1 hpair.2.2

end FalconerThetaGauge
