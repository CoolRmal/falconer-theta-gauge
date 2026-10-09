module

public import FalconerThetaGauge.SpaceSplittingFarCasesGeometry
public import FalconerThetaGauge.SpaceSplittingKernelPointwise

/-! # The actual far comparable indicator on the extended passing-distance kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

def spaceSplittingFarWeightedKernel (p v : ℕ) (Z₁ Z₂ : Set (Plane × Plane)) :
    (Plane × Plane) × (Plane × Plane) → ℝ≥0∞ :=
  (spaceSplittingFarComparableSet p).indicator
    (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z₁ Z₂)

@[fun_prop]
theorem measurable_spaceSplittingFarWeightedKernel (p v : ℕ)
    {Z₁ Z₂ : Set (Plane × Plane)} (hZ₁ : MeasurableSet Z₁) (hZ₂ : MeasurableSet Z₂) :
    Measurable (spaceSplittingFarWeightedKernel p v Z₁ Z₂) :=
  (measurable_spaceSplittingWeightedKernel _ hZ₁ hZ₂).indicator
    (measurableSet_spaceSplittingFarComparableSet p)

theorem ofReal_spaceSplitting_passing_coefficient_eq_weighted
    {x x' y y' : Plane} (hdx : 0 < dist x x') (hdy : 0 < dist y y')
    (Z₁ Z₂ : Set (Plane × Plane)) (v : ℕ) :
    ENNReal.ofReal (((2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v /
      Real.sqrt (dist x x' * dist y y') /
        (1 + (2 : ℝ) ^ v * |dist x x' - dist y y'|) ^ 2) *
          Z₁.indicator (fun _ ↦ (1 : ℝ)) (x, x') *
          Z₂.indicator (fun _ ↦ (1 : ℝ)) (y, y')) =
      ENNReal.ofReal ((2 : ℝ) ^ (25 : ℕ)) * ENNReal.ofReal ((2 : ℝ) ^ v) *
        spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ))) Z₁ Z₂ ((x, x'), (y, y')) := by
  rw [spaceSplittingWeightedKernel_eq_ofReal hdx hdy,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end FalconerThetaGauge
