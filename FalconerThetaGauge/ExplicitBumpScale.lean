module

public import FalconerThetaGauge.ExplicitBump
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Rescaled quantitative finite-order smooth kernels -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The order-`K` probability kernel at the actual positive spatial scale `δ`. -/
def scaledExplicitBump (K : ℕ) (δ : ℝ) (x : ℝ) : ℝ :=
  δ⁻¹ * explicitBump K (δ⁻¹ * x)

theorem contDiff_scaledExplicitBump (K : ℕ) (δ : ℝ) :
    ContDiff ℝ ∞ (scaledExplicitBump K δ) := by
  change ContDiff ℝ ∞ (fun x : ℝ ↦ δ⁻¹ * explicitBump K (δ⁻¹ * x))
  exact contDiff_const.mul ((contDiff_explicitBump K).comp
    (contDiff_const.mul contDiff_id))

theorem hasCompactSupport_scaledExplicitBump (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (scaledExplicitBump K δ) := by
  have h := (hasCompactSupport_explicitBump K).comp_homeomorph
    (Homeomorph.mulLeft₀ δ⁻¹ (inv_ne_zero hδ.ne'))
  exact h.mul_left (f := fun _ : ℝ ↦ δ⁻¹)

theorem scaledExplicitBump_nonneg (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ scaledExplicitBump K δ x :=
  mul_nonneg (inv_nonneg.mpr hδ.le) (explicitBump_nonneg K _)

theorem scaledExplicitBump_even (K : ℕ) (δ x : ℝ) :
    scaledExplicitBump K δ (-x) = scaledExplicitBump K δ x := by
  simp only [scaledExplicitBump, mul_neg, explicitBump_even]

theorem integral_scaledExplicitBump (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, scaledExplicitBump K δ x) = 1 := by
  change (∫ x : ℝ, δ⁻¹ * explicitBump K (δ⁻¹ * x)) = 1
  rw [integral_const_mul, Measure.integral_comp_inv_mul_left]
  simp only [abs_of_pos hδ, smul_eq_mul, integral_explicitBump, mul_one]
  exact inv_mul_cancel₀ hδ.ne'

theorem scaledExplicitBump_eq_zero_of_scale_lt_abs (K : ℕ) {δ x : ℝ}
    (hδ : 0 < δ) (hx : δ < |x|) : scaledExplicitBump K δ x = 0 := by
  have h : 1 < |δ⁻¹ * x| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hδ)]
    exact (one_lt_inv_mul₀ hδ).mpr hx
  simp only [scaledExplicitBump, explicitBump_eq_zero_of_one_lt_abs K h, mul_zero]

theorem iteratedDeriv_scaledExplicitBump (K k : ℕ) (δ x : ℝ) :
    iteratedDeriv k (scaledExplicitBump K δ) x =
      δ⁻¹ * (δ⁻¹ ^ k * iteratedDeriv k (explicitBump K) (δ⁻¹ * x)) := by
  change iteratedDeriv k (fun y : ℝ ↦ δ⁻¹ * explicitBump K (δ⁻¹ * y)) x = _
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_const_mul ((contDiff_explicitBump K).of_le (by simp))]

/-- Exact scaling of the derivative's true full-line `L¹` norm. -/
theorem integral_norm_iteratedDeriv_scaledExplicitBump (K k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    (∫ x : ℝ, ‖iteratedDeriv k (scaledExplicitBump K δ) x‖) =
      δ⁻¹ ^ k * ∫ x : ℝ, ‖iteratedDeriv k (explicitBump K) x‖ := by
  simp_rw [iteratedDeriv_scaledExplicitBump, norm_mul, Real.norm_eq_abs, abs_pow,
    abs_of_pos (inv_pos.mpr hδ)]
  rw [integral_const_mul, integral_const_mul]
  rw [Measure.integral_comp_inv_mul_left (fun x : ℝ ↦ |iteratedDeriv k (explicitBump K) x|) δ]
  simp only [abs_of_pos hδ, smul_eq_mul]
  field_simp

theorem integral_norm_iteratedDeriv_scaledExplicitBump_le (K k : ℕ) (hk : k ≤ K)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, ‖iteratedDeriv k (scaledExplicitBump K δ) x‖) ≤
      δ⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) := by
  rw [integral_norm_iteratedDeriv_scaledExplicitBump K k hδ]
  exact mul_le_mul_of_nonneg_left (integral_norm_iteratedDeriv_explicitBump_le K k hk)
    (pow_nonneg (inv_nonneg.mpr hδ.le) _)

end FalconerThetaGauge
