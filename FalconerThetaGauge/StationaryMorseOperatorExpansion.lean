module

public import FalconerThetaGauge.StationaryMorseL1Budget
public import FalconerThetaGauge.StationaryPhaseOperatorsComplex

/-! # The actual localized stationary expansion in universal operator form -/

@[expose] public section

noncomputable section

open Filter Finset
open scoped Topology ContDiff

namespace FalconerThetaGauge

theorem stationaryMorseAmplitude_eq_weighted_near_zero (K : ℕ) (G : ℝ → ℂ) (φ : ℝ) :
    stationaryMorseAmplitude (circularStationaryCutoff K) G φ =ᶠ[𝓝 0]
      (fun s ↦ G (φ + stationaryMorseAngle s) * stationaryMorseJacobian s) := by
  have hc : ContinuousAt (fun s ↦ |stationaryMorseAngle s|) 0 :=
    ((contDiffAt_stationaryMorseAngle (by norm_num)).continuousAt).abs
  have hh : ∀ᶠ s : ℝ in 𝓝 0, |stationaryMorseAngle s| < Real.pi / 6 := by
    exact hc.eventually (eventually_lt_nhds (by
      simpa only [stationaryMorseAngle_zero, abs_zero] using
        (by positivity : (0 : ℝ) < Real.pi / 6)))
  filter_upwards [hh] with s hs
  simp only [stationaryMorseAmplitude, circularStationaryCutoff_eq_one K hs.le,
    Complex.ofReal_one, one_mul]

theorem quadraticTaylorCoefficient_eq_operator_scale (Λ : ℝ) (j : ℕ) :
    quadraticTaylorCoefficient Λ j =
      (Λ : ℂ)⁻¹ ^ j * ((Complex.I / 2) ^ j / (j.factorial : ℂ)) := by
  simp only [quadraticTaylorCoefficient, div_eq_mul_inv, mul_inv, mul_pow]
  ring

theorem quadraticTaylorCoefficient_mul_morse_derivative {G : ℝ → ℂ} {j : ℕ}
    {φ : ℝ} (hG : ContDiffAt ℝ (2 * j) G φ) (K : ℕ) (Λ : ℝ) :
    quadraticTaylorCoefficient Λ j *
        iteratedDeriv (2 * j) (stationaryMorseAmplitude (circularStationaryCutoff K) G φ) 0 =
      (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j G φ := by
  rw [(stationaryMorseAmplitude_eq_weighted_near_zero K G φ).iteratedDeriv_eq (2 * j),
    stationaryPhaseOperator_eq_scaled_derivative hG, quadraticTaylorCoefficient_eq_operator_scale]
  ring

/-- Actual circular operators, actual smooth cutoffs, and a fully quantified localized error. -/
theorem localizedCircleIntegral_operator_expansion {T : ℕ} {G : ℝ → ℂ} {A M φ Λ : ℝ}
    (hG : IsDerivativeRegular A M (2 * T + 2) G) (hGsmooth : ContDiff ℝ ∞ G)
    (hΛ : 0 < Λ) :
    ‖localizedCircleIntegral (circularStationaryCutoff (2 * T + 2)) G φ Λ -
      Complex.exp (-(Λ : ℂ) * Complex.I) * quadraticPhasePrefactor Λ *
        ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j G φ‖ ≤
      Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        (4 * A * (56 * M) ^ (2 * T) * ((2 * T).factorial : ℝ) ^ 2 +
          4 * A * (56 * M) ^ (2 * T + 2) * ((2 * T + 2).factorial : ℝ) ^ 2) := by
  have h := localizedCircleIntegral_expansion_uniform (φ := φ) hG hGsmooth hΛ
  have he : (∑ j ∈ range T, quadraticTaylorCoefficient Λ j *
      iteratedDeriv (2 * j)
        (stationaryMorseAmplitude (circularStationaryCutoff (2 * T + 2)) G φ) 0) =
      ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j G φ := by
    apply sum_congr rfl
    intro j _
    have hj : ContDiffAt ℝ (2 * j : ℕ) G φ := hGsmooth.contDiffAt.of_le (by
      exact WithTop.coe_le_coe.mpr (le_top : ((2 * j : ℕ) : ℕ∞) ≤ ⊤))
    exact quadraticTaylorCoefficient_mul_morse_derivative
      hj _ _
  rwa [he] at h

end FalconerThetaGauge
