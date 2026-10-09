module

public import FalconerThetaGauge.QuadraticPhaseFourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual Schwartz derivatives and their Fourier moments

Iterating the Schwartz derivative keeps every derivative integrable. Its
inverse transform is the original transform times the exact frequency power.
-/

@[expose] public section

noncomputable section

open MeasureTheory Function LineDeriv
open scoped FourierTransform RealInnerProductSpace

namespace FalconerThetaGauge

def schwartzIteratedDeriv (k : ℕ) (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ)^[k] g

theorem schwartzIteratedDeriv_apply (k : ℕ) (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzIteratedDeriv k g x = iteratedDeriv k g x := by
  induction k generalizing x with
  | zero => simp [schwartzIteratedDeriv]
  | succ k ih =>
    change (SchwartzMap.derivCLM ℂ ℂ)^[k + 1] g x = _
    rw [Function.iterate_succ_apply', SchwartzMap.derivCLM_apply, iteratedDeriv_succ]
    congr 1
    exact funext ih

theorem fourierInv_schwartz_deriv (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (𝓕⁻ (SchwartzMap.derivCLM ℂ ℂ g)) ξ =
      (-2 * (Real.pi : ℂ) * Complex.I * ξ) * (𝓕⁻ g) ξ := by
  have hD : SchwartzMap.derivCLM ℂ ℂ g = ∂_{(1 : ℝ)} g := by
    ext x
    rw [SchwartzMap.derivCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [hD, SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply, Real.inner_apply, mul_one]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

theorem fourierInv_schwartzIteratedDeriv (k : ℕ) (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (𝓕⁻ (schwartzIteratedDeriv k g)) ξ =
      (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ k * (𝓕⁻ g) ξ := by
  induction k with
  | zero => simp [schwartzIteratedDeriv]
  | succ k ih =>
    change (𝓕⁻ ((SchwartzMap.derivCLM ℂ ℂ)^[k + 1] g)) ξ = _
    rw [Function.iterate_succ_apply', fourierInv_schwartz_deriv]
    change _ * (𝓕⁻ (schwartzIteratedDeriv k g)) ξ = _
    rw [ih, pow_succ]
    ring

theorem integral_fourierInv_schwartz (g : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, (𝓕⁻ g) ξ) = g 0 := by
  have heq : 𝓕 (𝓕⁻ g : SchwartzMap ℝ ℂ) = g := FourierTransform.fourier_fourierInv_eq g
  have h := congrArg (fun f : SchwartzMap ℝ ℂ ↦ f 0) heq
  rw [SchwartzMap.fourier_coe, Real.fourier_eq] at h
  simpa using h

theorem integral_fourierInv_derivative_moment (k : ℕ) (g : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ k * (𝓕⁻ g) ξ) =
      iteratedDeriv k g 0 := by
  simp_rw [← fourierInv_schwartzIteratedDeriv k g]
  rw [integral_fourierInv_schwartz, schwartzIteratedDeriv_apply]

theorem norm_fourierInv_le_integral_norm (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ‖(𝓕⁻ g) ξ‖ ≤ ∫ x : ℝ, ‖g x‖ := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp only [Circle.norm_smul]

theorem norm_fourierInv_derivative_power_le (k : ℕ) (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ k * (𝓕⁻ g) ξ‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv k g x‖ := by
  rw [← fourierInv_schwartzIteratedDeriv]
  simpa only [schwartzIteratedDeriv_apply] using
    norm_fourierInv_le_integral_norm (schwartzIteratedDeriv k g) ξ

theorem integrable_pow_mul_fourierInv (g : SchwartzMap ℝ ℂ) (k : ℕ) :
    Integrable (fun ξ : ℝ ↦ (ξ : ℂ) ^ k * (𝓕⁻ g) ξ) := by
  have hg : (fun ξ : ℝ ↦ ξ ^ k).HasTemperateGrowth := by fun_prop
  have h := (SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ ↦ ξ ^ k) (𝓕⁻ g)).integrable
    (μ := volume)
  simpa only [SchwartzMap.smulLeftCLM_apply hg, Complex.real_smul,
    Complex.ofReal_pow] using h

end FalconerThetaGauge
