module

public import FalconerThetaGauge.StationaryMorseSubstitution

/-!
# The finite stationary expansion of the actual localized circle integral

The coefficients are the actual derivatives of the proved Morse amplitude.
Uniform operator and derivative bounds are separate subsequent estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem localizedCircleIntegral_expansion {χ : ℝ → ℝ} {G : ℝ → ℂ}
    (hχsmooth : ContDiff ℝ ∞ χ) (hG : ContDiff ℝ ∞ G)
    (hχ : ∀ t : ℝ, Real.pi / 3 < |t| → χ t = 0) (φ₀ : ℝ) {Λ : ℝ} (hΛ : 0 < Λ)
    (T : ℕ) :
    ‖localizedCircleIntegral χ G φ₀ Λ -
      Complex.exp (-(Λ : ℂ) * Complex.I) * quadraticPhasePrefactor Λ *
        ∑ j ∈ range T, quadraticTaylorCoefficient Λ j *
          iteratedDeriv (2 * j) (stationaryMorseAmplitude χ G φ₀) 0‖ ≤
      Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        ((∫ x : ℝ, ‖iteratedDeriv (2 * T) (stationaryMorseAmplitude χ G φ₀) x‖) +
          (∫ x : ℝ, ‖iteratedDeriv (2 * T + 2) (stationaryMorseAmplitude χ G φ₀) x‖)) := by
  rw [localizedCircleIntegral_eq_quadratic hχsmooth hG hχ, mul_assoc, ← mul_sub, norm_mul]
  have hnorm : ‖Complex.exp (-(Λ : ℂ) * Complex.I)‖ = 1 := by
    simpa only [Complex.ofReal_neg] using Complex.norm_exp_ofReal_mul_I (-Λ)
  rw [hnorm, one_mul, quadraticPhasePrefactor_eq hΛ]
  exact quadratic_phase_compact hΛ T (contDiff_stationaryMorseAmplitude hχsmooth hG hχ φ₀)
    (hasCompactSupport_stationaryMorseAmplitude hχ G φ₀)

end FalconerThetaGauge
