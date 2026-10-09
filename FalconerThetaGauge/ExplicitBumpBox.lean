module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Genuine box smoothing and its explicit derivative cost

The normalized average over a width-`2a` interval is the convolution with the
uniform box probability. The fundamental theorem of calculus identifies its
derivative with the signed endpoint difference. Each such difference costs at
most `a⁻¹` in the actual first norm, uniformly in the smooth input function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace FalconerThetaGauge

/-- The literal normalized uniform-box convolution, expressed as an interval integral. -/
def boxAverage (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * a)⁻¹ * ∫ t in (x - a)..(x + a), f t

/-- The actual signed endpoint difference produced by differentiating a box average. -/
def boxDifference (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * a)⁻¹ * (f (x + a) - f (x - a))

theorem hasDerivAt_boxAverage (a : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (boxAverage a f) (boxDifference a f x) x := by
  have hF (y : ℝ) : HasDerivAt (fun u ↦ ∫ t in (0 : ℝ)..u, f t) (f y) y :=
    (hf.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hright := (hF (x + a)).comp x ((hasDerivAt_id x).add_const a)
  have hleft := (hF (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  have havg : boxAverage a f = fun y ↦ (2 * a)⁻¹ *
      ((∫ t in (0 : ℝ)..(y + a), f t) - ∫ t in (0 : ℝ)..(y - a), f t) := by
    funext y
    unfold boxAverage
    congr 1
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (0 : ℝ) (y - a))
      (hf.intervalIntegrable (μ := volume) (y - a) (y + a))
    linarith
  rw [havg]
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, mul_one, boxDifference] using
    (hright.sub hleft).const_mul ((2 * a)⁻¹)

theorem deriv_boxAverage (a : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    deriv (boxAverage a f) = boxDifference a f := by
  funext x
  exact (hasDerivAt_boxAverage a hf x).deriv

/-- Box convolution of a genuine smooth input remains smooth. -/
theorem contDiff_boxAverage (a : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (boxAverage a f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_boxAverage a hf.continuous x).differentiableAt, ?_⟩
  rw [deriv_boxAverage a hf.continuous]
  unfold boxDifference
  fun_prop

/-- Translation does not change the genuine first-norm integral. -/
theorem integral_norm_translate (f : ℝ → ℝ) (a : ℝ) :
    (∫ x : ℝ, ‖f (x + a)‖) = ∫ x : ℝ, ‖f x‖ :=
  integral_add_right_eq_self (fun x ↦ ‖f x‖) a

theorem integrable_boxDifference (a : ℝ) {f : ℝ → ℝ} (hf : Integrable f volume) :
    Integrable (boxDifference a f) volume := by
  have hright := (measurePreserving_add_right (volume : Measure ℝ) a).integrable_comp hf.aestronglyMeasurable
  have hleft := (measurePreserving_add_right (volume : Measure ℝ) (-a)).integrable_comp hf.aestronglyMeasurable
  have hr : Integrable (fun x : ℝ ↦ f (x + a)) volume := hright.mpr hf
  have hl : Integrable (fun x : ℝ ↦ f (x - a)) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using hleft.mpr hf
  exact (hr.sub hl).const_mul ((2 * a)⁻¹)

/-- Differentiating one normalized box costs precisely `a⁻¹` in `L¹`. -/
theorem integral_norm_boxDifference_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    (∫ x : ℝ, ‖boxDifference a f x‖) ≤ a⁻¹ * ∫ x : ℝ, ‖f x‖ := by
  have hr : Integrable (fun x : ℝ ↦ f (x + a)) volume :=
    ((measurePreserving_add_right (volume : Measure ℝ) a).integrable_comp hf.aestronglyMeasurable).mpr hf
  have hl : Integrable (fun x : ℝ ↦ f (x - a)) volume := by
    have h := ((measurePreserving_add_right (volume : Measure ℝ) (-a)).integrable_comp hf.aestronglyMeasurable).mpr hf
    simpa only [Function.comp_def, sub_eq_add_neg] using h
  calc
    _ ≤ ∫ x : ℝ, (2 * a)⁻¹ * (‖f (x + a)‖ + ‖f (x - a)‖) := by
      apply integral_mono (integrable_boxDifference a hf).norm ((hr.norm.add hl.norm).const_mul _)
      intro x
      simp only [boxDifference, norm_mul, Real.norm_eq_abs,
        Pi.add_apply, abs_of_pos (show (0 : ℝ) < (2 * a)⁻¹ by positivity)]
      simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left
        (norm_sub_le (f (x + a)) (f (x - a)))
        (show (0 : ℝ) ≤ (2 * a)⁻¹ by positivity)
    _ = (2 * a)⁻¹ * ((∫ x : ℝ, ‖f (x + a)‖) + ∫ x : ℝ, ‖f (x - a)‖) := by
      rw [integral_const_mul, integral_add hr.norm hl.norm]
    _ = _ := by
      rw [integral_norm_translate]
      have hleft : (∫ x : ℝ, ‖f (x - a)‖) = ∫ x : ℝ, ‖f x‖ := by
        simpa only [sub_eq_add_neg] using integral_norm_translate f (-a)
      rw [hleft]
      field_simp
      ring

end FalconerThetaGauge
