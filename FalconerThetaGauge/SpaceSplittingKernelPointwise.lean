module

public import FalconerThetaGauge.SpaceSplittingWeightedKernel
public import FalconerThetaGauge.SpaceSplittingOppositeSupport
public import FalconerThetaGauge.SpaceSplittingBudget

/-! # The actual stationary kernel is the extended weighted distance kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

theorem scalarBinningKernel_dyadic (v : ℕ) (dx dy : ℝ) :
    scalarBinningKernel ((2 : ℝ) ^ (-(v : ℝ))) (dx, dy) =
      ENNReal.ofReal ((1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2)⁻¹ := by
  have hs : 0 < (2 : ℝ) ^ v := by positivity
  unfold scalarBinningKernel
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp only [div_inv_eq_mul, mul_comm |dx - dy|]
  rw [Real.rpow_neg (by positivity), Real.rpow_two,
    ENNReal.ofReal_inv_of_pos (by positivity)]

theorem spaceSplittingWeightedKernel_eq_ofReal {x x' y y' : Plane}
    (hdx : 0 < dist x x') (hdy : 0 < dist y y')
    (Z₁ Z₂ : Set (Plane × Plane)) (v : ℕ) :
    spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z₁ Z₂ ((x, x'), (y, y')) =
      ENNReal.ofReal ((Real.sqrt (dist x x' * dist y y'))⁻¹ /
        (1 + (2 : ℝ) ^ v * |dist x x' - dist y y'|) ^ 2 *
          Z₁.indicator (fun _ ↦ 1) (x, x') * Z₂.indicator (fun _ ↦ 1) (y, y')) := by
  have h₁ : 0 ≤ Z₁.indicator (fun _ ↦ (1 : ℝ)) (x, x') :=
    indicator_nonneg (fun _ _ ↦ by norm_num) _
  have h₂ : 0 ≤ Z₂.indicator (fun _ ↦ (1 : ℝ)) (y, y') :=
    indicator_nonneg (fun _ _ ↦ by norm_num) _
  unfold spaceSplittingWeightedKernel
  rw [crossDistanceWeight_eq_ofReal (dist_pos.1 hdx),
    crossDistanceWeight_eq_ofReal (dist_pos.1 hdy), scalarBinningKernel_dyadic]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.sqrt_mul hdx.le]
  ring

/-- The source coefficient bound is expressed by the genuine extended weighted kernel. -/
theorem ofReal_norm_spaceSplittingBuiltOppositeSeries_le
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i : ℕ) {radialOrder v T : ℕ} (hK : 2 ≤ radialOrder)
    (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I) {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) (8 * T) I (2 * T))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) (8 * T) I (2 * T))
    {x x' y y' : Plane} (hdx : 0 < dist x x') (hdy : 0 < dist y y')
    (hxscale : 1600 * T * (max 1 (scheduledSymbolScale T E I L)) ^ 2 /
      ((2 : ℝ) ^ v * dist x x') ≤ 1 / 4)
    (hyscale : 1600 * T * (max 1 (scheduledSymbolScale T E I L)) ^ 2 /
      ((2 : ℝ) ^ v * dist y y') ≤ 1 / 4) :
    ENNReal.ofReal ‖spaceSplittingBuiltOppositeSeries radialOrder v T b₁ b₂ x x' y y'‖ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (25 : ℕ)) * ENNReal.ofReal ((2 : ℝ) ^ v) *
        spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ)))
          (scheduledPassingPairSet ρ ρ E (directionalLevelWidth levels (i + 1)) I I)
          (scheduledPassingPairSet ρ ρ E (directionalLevelWidth levels (i + 1)) I I)
          ((x, x'), (y, y')) := by
  have h := norm_spaceSplittingBuiltOppositeSeries_le_passing_kernel ρ E hlevels hsize
    i hK I hordered hL hb₁ hb₂ hdx hdy hxscale hyscale
  apply (ENNReal.ofReal_le_ofReal h).trans_eq
  rw [spaceSplittingWeightedKernel_eq_ofReal hdx hdy,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end FalconerThetaGauge
