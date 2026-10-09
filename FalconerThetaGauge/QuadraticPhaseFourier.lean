module

public import FalconerThetaGauge.QuadraticPhaseDuality
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Fourier identity for an actual quadratic phase

The Gaussian limit is specialized to the literal real phase. Its prefactor
has the sharp square-root norm, with the chosen complex branch explicit.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace FalconerThetaGauge

def quadraticPhasePrefactor (Λ : ℝ) : ℂ :=
  ((Real.pi : ℂ) / (-((Λ / 2 : ℝ) : ℂ) * Complex.I)) ^ (1 / 2 : ℂ)

theorem norm_quadraticPhasePrefactor {Λ : ℝ} (hΛ : 0 < Λ) :
    ‖quadraticPhasePrefactor Λ‖ = Real.sqrt (2 * Real.pi / Λ) := by
  have hhalf : (0 : ℝ) < Λ / 2 := by positivity
  have he : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [quadraticPhasePrefactor, he, Complex.norm_cpow_real, norm_div, norm_mul,
    norm_neg, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hhalf,
    Real.sqrt_eq_rpow]
  congr 1
  field_simp

/-- The quadratic Fourier identity in Mathlib's normalized frequency variable. -/
theorem quadratic_phase_fourier_identity {Λ : ℝ} (hΛ : 0 < Λ) (g : SchwartzMap ℝ ℂ) :
    (∫ s : ℝ, Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) * g s) =
      quadraticPhasePrefactor Λ * ∫ ξ : ℝ,
        Complex.exp (-((2 * Real.pi ^ 2 / Λ * ξ ^ 2 : ℝ) : ℂ) * Complex.I) * (𝓕⁻ g) ξ := by
  let b : ℂ := -((Λ / 2 : ℝ) : ℂ) * Complex.I
  have hre : b.re = 0 := by simp [b]
  have him : b.im ≠ 0 := by
    simp only [b, Complex.mul_im, Complex.neg_re, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.neg_im, Complex.ofReal_im, neg_zero,
      Complex.I_re, mul_zero, add_zero, neg_ne_zero]
    exact div_ne_zero hΛ.ne' (by norm_num)
  have h := integral_quadraticGaussian_mul_schwartz_of_re_zero hre him g
  have hspatial : quadraticGaussian b = fun s : ℝ ↦
      Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) := by
    funext s
    unfold quadraticGaussian
    congr 1
    dsimp [b]
    push_cast
    ring
  have hdual : ∀ ξ : ℝ, Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b) =
      Complex.exp (-((2 * Real.pi ^ 2 / Λ * ξ ^ 2 : ℝ) : ℂ) * Complex.I) := by
    intro ξ
    congr 1
    dsimp [b]
    push_cast
    field_simp
    simp only [Complex.I_sq]
    ring
  simp_rw [hdual] at h
  simpa only [hspatial, quadraticPhasePrefactor, b] using h

end FalconerThetaGauge
