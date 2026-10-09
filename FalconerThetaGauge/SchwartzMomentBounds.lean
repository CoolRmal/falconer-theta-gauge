module

public import FalconerThetaGauge.SchwartzDerivatives
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrable frequency moments from two actual derivative norms

The adjacent derivative bounds give a Cauchy majorant. Its exact integral
controls the frequency moment with the constant one half in the normalized
Fourier variable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace FalconerThetaGauge

theorem norm_quadraticFrequency_sq (ξ : ℝ) :
    ‖-2 * (Real.pi : ℂ) * Complex.I * ξ‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 := by
  have he : (-2 * (Real.pi : ℂ) * Complex.I * ξ) =
      ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, sq_abs]
  ring

/-- A frequency moment is integrable and controlled by two adjacent derivative norms. -/
theorem integral_fourierInv_derivative_power_le (k : ℕ) (g : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ k * (𝓕⁻ g) ξ‖) ≤
      ((∫ x : ℝ, ‖iteratedDeriv k g x‖) +
        (∫ x : ℝ, ‖iteratedDeriv (k + 2) g x‖)) / 2 := by
  let A := ∫ x : ℝ, ‖iteratedDeriv k g x‖
  let B := ∫ x : ℝ, ‖iteratedDeriv (k + 2) g x‖
  let F := fun ξ : ℝ ↦ ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ k * (𝓕⁻ g) ξ‖
  have hFint : Integrable F := by
    simpa only [F, ← fourierInv_schwartzIteratedDeriv k g] using
      (𝓕⁻ (schwartzIteratedDeriv k g)).integrable.norm
  have hmajor : ∀ ξ, F ξ ≤ (A + B) * (1 + (2 * Real.pi * ξ) ^ 2)⁻¹ := by
    intro ξ
    have h₀ := norm_fourierInv_derivative_power_le k g ξ
    have h₂ := norm_fourierInv_derivative_power_le (k + 2) g ξ
    have hid : F ξ * (2 * Real.pi * ξ) ^ 2 =
        ‖(-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ (k + 2) * (𝓕⁻ g) ξ‖ := by
      rw [← norm_quadraticFrequency_sq]
      dsimp [F]
      simp only [norm_mul, norm_pow, pow_add]
      ring
    have hsum : F ξ * (1 + (2 * Real.pi * ξ) ^ 2) ≤ A + B := by
      calc
        _ = F ξ + F ξ * (2 * Real.pi * ξ) ^ 2 := by ring
        _ ≤ A + B := add_le_add h₀ (by simpa only [hid] using h₂)
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).mpr hsum
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hmajint : Integrable (fun ξ : ℝ ↦ (A + B) * (1 + (2 * Real.pi * ξ) ^ 2)⁻¹) :=
    (integrable_inv_one_add_mul_sq hpi).const_mul _
  calc
    _ ≤ ∫ ξ : ℝ, (A + B) * (1 + (2 * Real.pi * ξ) ^ 2)⁻¹ :=
      integral_mono hFint hmajint hmajor
    _ = _ := by
      rw [integral_const_mul, integral_univ_inv_one_add_mul_sq,
        abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      dsimp [A, B]
      field_simp

end FalconerThetaGauge
