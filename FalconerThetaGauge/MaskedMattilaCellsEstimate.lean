/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaNormalizedEstimate
public import FalconerThetaGauge.MaskedMattilaGeometry

/-! # Source Estimate 7.5 on the actual occupied separated dyadic cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

set_option maxHeartbeats 800000 in
theorem levelMaskedDistance_mattila_cells_estimate {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    {a : ℕ} {P Q : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a P Q)
    (hP : P ∈ occupiedUnitCells ρ₁ a) (hQ : Q ∈ occupiedUnitCells ρ₂ a)
    (levels i : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) (cutoffK v : ℕ) (hv : v ≤ N)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - a)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N) :
    scalarDyadicFourierShellIntegral
        (levelMaskedDistanceMeasure ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
          (tolerance θ N * N) levels i (8 * expansionCount θ N) I₁ I₂) v /
        (ρ₁.real (dyadicCube a P) * ρ₂.real (dyadicCube a Q)) ≤
      2 * scheduledFourierEnergySup ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
        (tolerance θ N * N) (directionalLevelWidth levels i)
        (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v +
      (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  have hballs := source_spatial_separated_balls_cells hsep
  have hm : 0 < ρ₁.real (dyadicCube a P) * ρ₂.real (dyadicCube a Q) :=
    mul_pos (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2
  have ha : a ≤ N := by
    have hE := hpar.2.2.1.1
    have hvr : (v : ℝ) ≤ N := by exact_mod_cast hv
    have har : (a : ℝ) ≤ N := by linarith
    exact_mod_cast har
  rw [← builtMaskedDistanceMeasure_eq_level ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)]
  apply builtMaskedDistance_mattila_shell_normalized_estimate hpar ρ₁ ρ₂
    hballs.1 hballs.2 (measurableSet_dyadicCube a P) (measurableSet_dyadicCube a Q) hm
    (dyadicCube_subset_closedBall_twice_radius a P)
    (dyadicCube_subset_closedBall_twice_radius a Q) (directionalLevelWidth levels i)
    (radialAngle (dyadicCellCenter a Q) (dyadicCellCenter a P)) (a : ℝ)
    I₁ I₂ hL₁ hL₂ hc₁ hc₂ hL₁N hL₂N cutoffK v hv
    (source_spatial_inverse_coefficient_cells hsep)
    (fun _x hx _y hy ↦ pairDirection_mem_arc_of_separatedDyadicCells hsep hx hy)
    hw hlength₁ hlength₂
  · intro r hr x hx y hy
    apply source_frequency_distance_lower hr
    simpa only [dist_eq_norm] using source_pair_distance_lower_cells hsep hx hy
  · intro x hx y hy
    apply source_pair_distance_terminal_lower ha
    simpa only [dist_eq_norm] using source_pair_distance_lower_cells hsep hx hy

end FalconerThetaGauge
