module

public import FalconerThetaGauge.StationaryMorseDerivativeBudget
public import FalconerThetaGauge.LocalizedStationaryPhase
public import FalconerThetaGauge.NonstationaryPhaseBounds

/-! # Literal integral derivative bounds for localized stationary phase -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The actual integral of the derivative norm is bounded by its support length. -/
theorem integral_norm_iteratedDeriv_stationaryMorseAmplitude_le {K k : ℕ} (hk : k ≤ K)
    {G : ℝ → ℂ} {A M φ : ℝ} (hG : IsDerivativeRegular A M K G) :
    (∫ s : ℝ, ‖iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ) s‖) ≤
      4 * A * (56 * M) ^ k * (k.factorial : ℝ) ^ 2 := by
  let bound := 2 * A * (56 * M) ^ k * (k.factorial : ℝ) ^ 2
  have hsupport : tsupport
      (iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ)) ⊆
        Icc (-1 : ℝ) 1 := by
    apply (tsupport_iteratedDeriv_subset k _).trans
    exact closure_minimal
      (support_stationaryMorseAmplitude_subset
        (fun _ hx ↦ circularStationaryCutoff_eq_zero K hx) G φ) isClosed_Icc
  have hmajor : ∀ s : ℝ,
      ‖iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ) s‖ ≤
        (Icc (-1 : ℝ) 1).indicator (fun _ ↦ bound) s := by
    intro s
    by_cases hs : s ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hs]
      exact norm_iteratedDeriv_stationaryMorseAmplitude_le hk hG (abs_le.mpr hs)
    · rw [indicator_of_notMem hs, image_eq_zero_of_notMem_tsupport
        (fun ht ↦ hs (hsupport ht)), norm_zero]
  have hi : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ ↦ bound)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (isCompact_Icc.measure_ne_top))
  calc
    _ ≤ ∫ s : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ ↦ bound) s :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
        hi (Filter.Eventually.of_forall hmajor)
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_Icc]
      have hv : volume.real (Icc (-1 : ℝ) 1) = 2 := by
        norm_num [Measure.real, Real.volume_Icc]
      simp only [hv, smul_eq_mul, bound]
      ring

/-- The localized circular stationary expansion now has a completely explicit actual remainder. -/
theorem localizedCircleIntegral_expansion_uniform {T : ℕ} {G : ℝ → ℂ} {A M φ Λ : ℝ}
    (hG : IsDerivativeRegular A M (2 * T + 2) G) (hGsmooth : ContDiff ℝ ∞ G)
    (hΛ : 0 < Λ) :
    ‖localizedCircleIntegral (circularStationaryCutoff (2 * T + 2)) G φ Λ -
      Complex.exp (-(Λ : ℂ) * Complex.I) * quadraticPhasePrefactor Λ *
        ∑ j ∈ Finset.range T, quadraticTaylorCoefficient Λ j *
          iteratedDeriv (2 * j)
            (stationaryMorseAmplitude (circularStationaryCutoff (2 * T + 2)) G φ) 0‖ ≤
      Real.sqrt (2 / Λ) * (2 * Λ)⁻¹ ^ T / (T.factorial : ℝ) *
        (4 * A * (56 * M) ^ (2 * T) * ((2 * T).factorial : ℝ) ^ 2 +
          4 * A * (56 * M) ^ (2 * T + 2) * ((2 * T + 2).factorial : ℝ) ^ 2) := by
  have h := localizedCircleIntegral_expansion
    (contDiff_circularStationaryCutoff (2 * T + 2)) hGsmooth
    (fun _ hx ↦ circularStationaryCutoff_eq_zero (2 * T + 2) hx) φ hΛ T
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add
      (integral_norm_iteratedDeriv_stationaryMorseAmplitude_le (by omega) hG)
      (integral_norm_iteratedDeriv_stationaryMorseAmplitude_le le_rfl hG)) (by positivity))

end FalconerThetaGauge
