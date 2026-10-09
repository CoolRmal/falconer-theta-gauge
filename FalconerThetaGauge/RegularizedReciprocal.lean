/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Smooth reciprocal construction adapted from falconer-packing; see docs/ATTRIBUTION.md.
-/
module

public import FalconerThetaGauge.NonstationaryReciprocal
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A smooth reciprocal with uniform derivative bounds

The reciprocal is cut off near zero. Its derivatives are bounded on a fixed compact interval;
outside that interval they are exactly the derivatives of the ordinary reciprocal.
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped ContDiff Topology

namespace FalconerThetaGauge

/-- A fixed smooth reciprocal, zero near the singularity. -/
noncomputable def regularizedReciprocal (x : ℝ) : ℝ :=
  Real.smoothTransition (4 * x ^ 2 - 1) / x

theorem regularizedReciprocal_eq_zero {x : ℝ} (hx : |x| ≤ 1 / 2) :
    regularizedReciprocal x = 0 := by
  have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [regularizedReciprocal, Real.smoothTransition.zero_of_nonpos (by nlinarith), zero_div]

theorem regularizedReciprocal_eq_inv {x : ℝ} (hx : 1 ≤ |x|) :
    regularizedReciprocal x = x⁻¹ := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  rw [regularizedReciprocal, Real.smoothTransition.one_of_one_le (by nlinarith), one_div]

/-- The cutoff cancels the singularity at zero, giving a globally smooth function. -/
theorem contDiff_regularizedReciprocal : ContDiff ℝ ∞ regularizedReciprocal := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro y hy
    exact regularizedReciprocal_eq_zero (by simpa only [dist_zero_right, Real.norm_eq_abs]
      using hy.le)
  · have hnum : ContDiff ℝ ∞ (fun y : ℝ ↦ Real.smoothTransition (4 * y ^ 2 - 1)) :=
      Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const)
    exact hnum.contDiffAt.div contDiffAt_id hx

end FalconerThetaGauge
