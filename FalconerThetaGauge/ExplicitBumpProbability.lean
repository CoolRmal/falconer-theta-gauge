module

public import FalconerThetaGauge.ExplicitBumpBox
public import Mathlib.Analysis.Convolution

/-!
# Normalized box smoothing preserves genuine probability densities

The interval average is identified with convolution against the actual uniform
box probability. It preserves positivity, mass, evenness, smoothness, and the
explicit additive support radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Convolution

namespace FalconerThetaGauge

def boxMeasure (a : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * a))⁻¹ • volume.restrict (Icc (-a) a)

theorem isProbabilityMeasure_boxMeasure {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (boxMeasure a) where
  measure_univ := by
    rw [boxMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
    have hlen : a - -a = 2 * a := by ring
    rw [hlen, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      ENNReal.ofReal_ne_top

theorem boxAverage_eq_integral_boxMeasure {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (x : ℝ) :
    boxAverage a f x = ∫ y, f (x - y) ∂boxMeasure a := by
  rw [boxMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * a), smul_eq_mul,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    intervalIntegral.integral_comp_sub_left]
  simp only [sub_neg_eq_add, boxAverage]

theorem boxAverage_eq_convolution {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    boxAverage a f = (fun _ : ℝ ↦ (1 : ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, boxMeasure a] f := by
  funext x
  rw [boxAverage_eq_integral_boxMeasure ha]
  simp only [convolution, ContinuousLinearMap.mul_apply', one_mul]

theorem integrable_boxAverage {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : Integrable f volume) : Integrable (boxAverage a f) volume := by
  have := isProbabilityMeasure_boxMeasure ha
  have hp := (integrable_const (1 : ℝ) (μ := boxMeasure a)).convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hf
  rw [show boxAverage a f = (fun x ↦ ∫ y, f (x - y) ∂boxMeasure a) from
    funext (boxAverage_eq_integral_boxMeasure ha f)]
  simpa only [convolution, ContinuousLinearMap.mul_apply', one_mul] using hp.integral_prod_left

theorem integral_boxAverage {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : Integrable f volume) : (∫ x : ℝ, boxAverage a f x) = ∫ x : ℝ, f x := by
  have := isProbabilityMeasure_boxMeasure ha
  rw [boxAverage_eq_convolution ha]
  simpa only [integral_const, measure_univ, Measure.real, ENNReal.toReal_one, one_smul,
    ContinuousLinearMap.mul_apply', one_mul] using
    integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (integrable_const (1 : ℝ) (μ := boxMeasure a)) hf

theorem boxAverage_nonneg {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : ℝ) : 0 ≤ boxAverage a f x := by
  rw [boxAverage_eq_integral_boxMeasure ha]
  exact integral_nonneg fun y ↦ hf (x - y)

theorem boxAverage_even {a : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (x : ℝ) : boxAverage a f (-x) = boxAverage a f x := by
  unfold boxAverage
  congr 1
  have h := intervalIntegral.integral_comp_sub_left (a := x - a) (b := x + a) f 0
  have hleft : (0 : ℝ) - (x + a) = -x - a := by ring
  have hright : (0 : ℝ) - (x - a) = -x + a := by ring
  simpa only [zero_sub, hf, hleft, hright] using h.symm

/-- Smoothing expands the support radius by exactly the box half-width. -/
theorem boxAverage_eq_zero_of_abs_gt {a R : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ∀ x, R < |x| → f x = 0) {x : ℝ} (hx : R + a < |x|) : boxAverage a f x = 0 := by
  unfold boxAverage
  have hz : (∫ t in (x - a)..(x + a), f t) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith : x - a ≤ x + a)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht' : t ∈ Ioc (x - a) (x + a) := ht
    have hnear : |x - t| ≤ a := by
      rw [abs_le]
      constructor <;> linarith [ht'.1, ht'.2]
    have htriangle : |x| ≤ |t| + |x - t| := by
      simpa only [Real.norm_eq_abs, add_sub_cancel] using norm_add_le t (x - t)
    exact hf t (by linarith)
  rw [hz, mul_zero]

end FalconerThetaGauge
