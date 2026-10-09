module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# The stretched logarithmic gauge

The manuscript prescribes the gauge on `0 < r < 1` and at zero. Its extension to
larger radii is immaterial to Hausdorff measure; we choose the identity there.
-/

@[expose] public section

open scoped ENNReal

namespace FalconerThetaGauge

noncomputable section

/-- The expression defining the manuscript's gauge at positive radii below one. -/
def realGauge (θ r : ℝ) : ℝ := r * Real.exp (-(Real.log (1 / r)) ^ θ)

/-- The manuscript's gauge, extended by `r` at radii at least one. -/
def thetaGauge (θ : ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r < 1 then ENNReal.ofReal (realGauge θ r.toReal) else r

@[simp]
theorem realGauge_zero (θ : ℝ) : realGauge θ 0 = 0 := by
  simp [realGauge]

theorem realGauge_pos (θ : ℝ) {r : ℝ} (hr : 0 < r) : 0 < realGauge θ r := by
  exact mul_pos hr (Real.exp_pos _)

theorem realGauge_nonneg (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ realGauge θ r := by
  exact mul_nonneg hr (Real.exp_pos _).le

theorem realGauge_le (θ : ℝ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    realGauge θ r ≤ r := by
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := lt_of_le_of_ne hr₀ (Ne.symm hr)
  have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg ((one_le_div₀ hrpos).mpr hr₁)
  have hexp : Real.exp (-(Real.log (1 / r)) ^ θ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg hlog θ))
  simpa [realGauge] using mul_le_mul_of_nonneg_left hexp hr₀

@[simp]
theorem thetaGauge_zero (θ : ℝ) : thetaGauge θ 0 = 0 := by
  simp [thetaGauge]

theorem thetaGauge_ofReal (θ : ℝ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    thetaGauge θ (ENNReal.ofReal r) = ENNReal.ofReal (realGauge θ r) := by
  have hr : ENNReal.ofReal r < 1 := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hr₁
  simp [thetaGauge, hr, ENNReal.toReal_ofReal hr₀]

theorem thetaGauge_pos (θ : ℝ) {r : ℝ≥0∞} (hr : 0 < r) : 0 < thetaGauge θ r := by
  unfold thetaGauge
  split_ifs with h
  · exact ENNReal.ofReal_pos.mpr (realGauge_pos θ (ENNReal.toReal_pos hr.ne' h.ne_top))
  · exact hr

theorem thetaGauge_le (θ : ℝ) (r : ℝ≥0∞) : thetaGauge θ r ≤ r := by
  unfold thetaGauge
  split_ifs with h
  · have hreal : r.toReal < 1 := by
      exact ENNReal.toReal_lt_of_lt_ofReal (by simpa using h)
    exact (ENNReal.ofReal_le_ofReal
      (realGauge_le θ ENNReal.toReal_nonneg hreal.le)).trans ENNReal.ofReal_toReal_le
  · exact le_rfl

end

end FalconerThetaGauge
