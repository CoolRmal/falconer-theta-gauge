module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Damped quadratic Gaussian duality

Positive real damping makes both Fourier pairings ordinary Bochner integrals.
The evaluated Gaussian transform will supply the stationary-phase formula
after the damping tends to zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped FourierTransform RealInnerProductSpace Topology

namespace FalconerThetaGauge

def quadraticGaussian (b : ℂ) (x : ℝ) : ℂ := Complex.exp (-b * (x : ℂ) ^ 2)

theorem integrable_quadraticGaussian {b : ℂ} (hb : 0 < b.re) :
    Integrable (quadraticGaussian b) := by
  change Integrable (fun x : ℝ ↦ Complex.exp (-b * (x : ℂ) ^ 2))
  simpa only [zero_mul, add_zero] using integrable_cexp_quadratic hb 0 0

/-- The exact evaluated transform, in Mathlib's `2π` normalization. -/
theorem fourier_quadraticGaussian {b : ℂ} (hb : 0 < b.re) (ξ : ℝ) :
    𝓕 (quadraticGaussian b) ξ =
      ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, quadraticGaussian]
  have he : (fun x : ℝ ↦ Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) *
      Complex.exp (-b * (x : ℂ) ^ 2)) =
      fun x : ℝ ↦ Complex.exp (Complex.I * (-2 * (Real.pi : ℂ) * ξ) * x) *
        Complex.exp (-b * (x : ℂ) ^ 2) := by
    funext x
    congr 2
    push_cast
    ring
  rw [he, fourierIntegral_gaussian hb]
  congr 2
  field_simp
  ring

/-- Actual Fourier duality with a Schwartz test and positive complex damping. -/
theorem integral_quadraticGaussian_mul_schwartz {b : ℂ} (hb : 0 < b.re)
    (g : SchwartzMap ℝ ℂ) :
    (∫ x, quadraticGaussian b x * g x) =
      ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) *
        ∫ ξ : ℝ, Complex.exp (-((Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) / b) * (𝓕⁻ g) ξ := by
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner
    (integrable_quadraticGaussian hb) (𝓕⁻ g).integrable
  have hL : (innerₗ ℝ).flip = innerₗ ℝ := by ext; rfl
  rw [hL] at hflip
  change (∫ ξ, 𝓕 (quadraticGaussian b) ξ * (𝓕⁻ g) ξ) =
    ∫ x, quadraticGaussian b x * 𝓕 ((𝓕⁻ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) x at hflip
  have hf : (∫ ξ, 𝓕 (quadraticGaussian b) ξ * (𝓕⁻ g) ξ) =
      ∫ x, quadraticGaussian b x * g x := by
    simpa only [← SchwartzMap.fourier_coe,
      FourierTransform.fourier_fourierInv_eq] using hflip
  rw [← hf]
  simp_rw [fourier_quadraticGaussian hb, mul_assoc]
  exact integral_const_mul _ _

end FalconerThetaGauge
