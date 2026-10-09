module

public import FalconerThetaGauge.OrthogonalProjectionSmoothing

/-!
# Genuine Fourier tails of the concrete density approximants

The residual of the inverse Fourier density and the actual low-pass smoothing
is controlled by the high-frequency tail of the source measure. This supplies
the Plancherel step in the endpoint Orlicz density estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal

namespace FalconerThetaGauge

theorem norm_one_sub_reconstructionFrequencyCutoff_le_one (ξ : ℝ) :
    ‖1 - reconstructionFrequencyCutoff ξ‖ ≤ 1 := by
  change ‖(1 : ℂ) - (reconstructionFrequencyBump ξ : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr reconstructionFrequencyBump.le_one)]
  linarith [reconstructionFrequencyBump.nonneg (x := ξ)]

theorem measureLowpassFourier_residual_le (μ : Measure ℝ) (n : ℕ) (ξ : ℝ) :
    ‖measureFourier μ ξ - measureLowpassFourier μ n ξ‖ ^ 2 ≤
      {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|}.indicator
        (fun ξ ↦ ‖measureFourier μ ξ‖ ^ 2) ξ := by
  by_cases hξ : |2 * Real.pi * ξ| ≤ (2 : ℝ) ^ n
  · rw [measureLowpassFourier, fourier_reconstructionLowpass_eq_one hξ]
    rw [indicator_of_notMem (show ξ ∉ {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|} from
      not_lt.mpr hξ)]
    simp
  · rw [indicator_of_mem (show ξ ∈ {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|} from
      lt_of_not_ge hξ), measureLowpassFourier, ← mul_one_sub, norm_mul, mul_pow,
      fourier_reconstructionLowpass]
    have h := norm_one_sub_reconstructionFrequencyCutoff_le_one
      ((2 * Real.pi * ξ) / (2 : ℝ) ^ n)
    have hs : ‖1 - reconstructionFrequencyCutoff ((2 * Real.pi * ξ) / (2 : ℝ) ^ n)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (1 - reconstructionFrequencyCutoff
        ((2 * Real.pi * ξ) / (2 : ℝ) ^ n))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (sq_nonneg ‖measureFourier μ ξ‖)

theorem integral_norm_sq_eq_Lp_norm_sq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x, ‖f x‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [Lp.norm_def]
  exact integral_norm_sq_eq_eLpNorm_two_sq (Lp.memLp f)

/-- The residual square norm is bounded by the actual measure Fourier tail. -/
theorem norm_density_lowpass_residual_sq_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : MemLp (measureFourier μ) 2 volume) (n : ℕ) :
    ‖measureFourierDensity μ hμ - measureLowpassDensityL2 μ n‖ ^ 2 ≤
      ∫ ξ in {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|}, ‖measureFourier μ ξ‖ ^ 2 := by
  have hs : MeasurableSet {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|} := by measurability
  let F := hμ.toLp (measureFourier μ) - measureLowpassFrequencyL2 μ n
  have hn : ‖measureFourierDensity μ hμ - measureLowpassDensityL2 μ n‖ = ‖F‖ := by
    change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (hμ.toLp (measureFourier μ)) -
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm (measureLowpassFrequencyL2 μ n)‖ = _
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  rw [hn, ← integral_norm_sq_eq_Lp_norm_sq F, ← integral_indicator hs]
  have hi : Integrable (fun ξ ↦ ‖measureFourier μ ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).mp hμ
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp F).aestronglyMeasurable).mp (Lp.memLp F))
    (hi.indicator hs)
  filter_upwards [Lp.coeFn_sub (hμ.toLp (measureFourier μ)) (measureLowpassFrequencyL2 μ n),
    hμ.coeFn_toLp, (memLp_measureLowpassFourier μ n).coeFn_toLp] with ξ hsub hfull hlow
  change ‖(hμ.toLp (measureFourier μ) - measureLowpassFrequencyL2 μ n) ξ‖ ^ 2 ≤ _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hfull, show measureLowpassFrequencyL2 μ n ξ = measureLowpassFourier μ n ξ from hlow]
  exact measureLowpassFourier_residual_le μ n ξ

def canonicalMeasureDensity (μ : Measure ℝ) (x : ℝ) : ℝ := (μ.rnDeriv volume x).toReal

@[fun_prop]
theorem measurable_canonicalMeasureDensity (μ : Measure ℝ) : Measurable (canonicalMeasureDensity μ) :=
  (Measure.measurable_rnDeriv μ volume).ennreal_toReal

theorem canonicalMeasureDensity_nonneg (μ : Measure ℝ) (x : ℝ) :
    0 ≤ canonicalMeasureDensity μ x := ENNReal.toReal_nonneg

theorem memLp_canonicalMeasureDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : MemLp (measureFourier μ) 2 volume) : MemLp (canonicalMeasureDensity μ) 2 volume := by
  apply (Lp.memLp (measureFourierDensity μ hμ)).congr_norm
    (measurable_canonicalMeasureDensity μ).aestronglyMeasurable
  filter_upwards [rnDeriv_ae_eq_measureFourierDensity μ hμ] with x hx
  rw [← hx]
  simp only [canonicalMeasureDensity, Complex.norm_real]

def orthogonalDensityTailThreshold (n : ℕ) : ℝ :=
  2 * (1 + orthogonalLowpassAmplitudeConstant) * (2 : ℝ) ^ n

theorem canonical_density_level_sq_le_residual (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (measureFourier μ) 2 volume) (n : ℕ) :
    ∀ᵐ x ∂volume, orthogonalDensityTailThreshold n < canonicalMeasureDensity μ x →
      canonicalMeasureDensity μ x ^ 2 ≤
        4 * ‖(measureFourierDensity μ hμ - measureLowpassDensityL2 μ n) x‖ ^ 2 := by
  filter_upwards [rnDeriv_ae_eq_measureFourierDensity μ hμ, measureLowpassDensityL2_ae_eq μ n,
    Lp.coeFn_sub (measureFourierDensity μ hμ) (measureLowpassDensityL2 μ n)]
    with x hx hlow hsub
  intro hlevel
  have hbound := norm_schwartzMeasureDensity_lowpass_le μ n x
  have htriangle : canonicalMeasureDensity μ x ≤
      ‖(canonicalMeasureDensity μ x : ℂ) - schwartzMeasureDensity μ (reconstructionLowpass n) x‖ +
        ‖schwartzMeasureDensity μ (reconstructionLowpass n) x‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (canonicalMeasureDensity_nonneg μ x)] using
        norm_le_norm_sub_add (canonicalMeasureDensity μ x : ℂ)
          (schwartzMeasureDensity μ (reconstructionLowpass n) x)
  have htwice : canonicalMeasureDensity μ x ≤
      2 * ‖(canonicalMeasureDensity μ x : ℂ) - schwartzMeasureDensity μ (reconstructionLowpass n) x‖ := by
    unfold orthogonalDensityTailThreshold at hlevel
    have hn : 0 < (2 : ℝ) ^ n := by positivity
    nlinarith
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [← hx, hlow]
  change canonicalMeasureDensity μ x ^ 2 ≤
    4 * ‖(canonicalMeasureDensity μ x : ℂ) - schwartzMeasureDensity μ (reconstructionLowpass n) x‖ ^ 2
  nlinarith [canonicalMeasureDensity_nonneg μ x,
    norm_nonneg ((canonicalMeasureDensity μ x : ℂ) - schwartzMeasureDensity μ (reconstructionLowpass n) x)]

/-- The actual high-density square mass is controlled by the inverse-Fourier residual. -/
theorem integral_canonical_density_level_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (measureFourier μ) 2 volume) (n : ℕ) :
    ∫ x in {x | orthogonalDensityTailThreshold n < canonicalMeasureDensity μ x},
      canonicalMeasureDensity μ x ^ 2 ≤
      4 * ‖measureFourierDensity μ hμ - measureLowpassDensityL2 μ n‖ ^ 2 := by
  have hs : MeasurableSet {x | orthogonalDensityTailThreshold n < canonicalMeasureDensity μ x} :=
    measurableSet_lt measurable_const (measurable_canonicalMeasureDensity μ)
  have hf : Integrable (fun x ↦ canonicalMeasureDensity μ x ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (measurable_canonicalMeasureDensity μ).aestronglyMeasurable).mp
        (memLp_canonicalMeasureDensity μ hμ)
  let R := measureFourierDensity μ hμ - measureLowpassDensityL2 μ n
  have hR : Integrable (fun x ↦ ‖R x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp R).aestronglyMeasurable).mp (Lp.memLp R)
  calc
    _ ≤ ∫ x in {x | orthogonalDensityTailThreshold n < canonicalMeasureDensity μ x},
        4 * ‖R x‖ ^ 2 := by
      apply integral_mono_ae hf.restrict (hR.const_mul _).restrict
      filter_upwards [ae_restrict_mem hs,
        ae_restrict_of_ae (canonical_density_level_sq_le_residual μ hμ n)] with x hx hlevel
      exact hlevel hx
    _ ≤ ∫ x, 4 * ‖R x‖ ^ 2 :=
      setIntegral_le_integral (hR.const_mul _) (Eventually.of_forall fun x ↦ by positivity)
    _ = _ := by rw [integral_const_mul, integral_norm_sq_eq_Lp_norm_sq]

theorem integral_canonical_density_level_le_fourier_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (measureFourier μ) 2 volume) (n : ℕ) :
    ∫ x in {x | orthogonalDensityTailThreshold n < canonicalMeasureDensity μ x},
      canonicalMeasureDensity μ x ^ 2 ≤
      4 * ∫ ξ in {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|}, ‖measureFourier μ ξ‖ ^ 2 :=
  (integral_canonical_density_level_le μ hμ n).trans
    (mul_le_mul_of_nonneg_left (norm_density_lowpass_residual_sq_le μ hμ n) (by norm_num))

theorem integral_measureFourier_tail_eq (μ : Measure ℝ) (n : ℕ) :
    ∫ ξ in {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|}, ‖measureFourier μ ξ‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ r in {r : ℝ | (2 : ℝ) ^ n < |r|}, ‖charFun μ r‖ ^ 2 := by
  have hS : MeasurableSet {r : ℝ | (2 : ℝ) ^ n < |r|} := by measurability
  have hS' : MeasurableSet {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|} := by measurability
  rw [← integral_indicator hS', ← integral_indicator hS]
  let f : ℝ → ℝ := {r : ℝ | (2 : ℝ) ^ n < |r|}.indicator (fun r ↦ ‖charFun μ r‖ ^ 2)
  have hchange : {ξ : ℝ | (2 : ℝ) ^ n < |2 * Real.pi * ξ|}.indicator
      (fun ξ ↦ ‖measureFourier μ ξ‖ ^ 2) = fun ξ ↦ f ((2 * Real.pi) * ξ) := by
    funext ξ
    simp only [f, indicator_apply, mem_ofPred_eq]
    by_cases hξ : (2 : ℝ) ^ n < |2 * Real.pi * ξ|
    · rw [ite_eq_left hξ, ite_eq_left hξ, measureFourier_eq_charFun,
        show -2 * Real.pi * ξ = -(2 * Real.pi * ξ) by ring,
        charFun_neg, RCLike.norm_conj]
    · rw [ite_eq_right hξ, ite_eq_right hξ]
  rw [hchange, Measure.integral_comp_mul_left f (2 * Real.pi)]
  rw [show |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ from
    abs_of_pos (inv_pos.mpr (by positivity))]
  rfl

theorem integral_canonical_density_level_le_charFun_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (charFun μ) 2 volume) (n : ℕ) :
    ∫ x in {x | orthogonalDensityTailThreshold n < canonicalMeasureDensity μ x},
      canonicalMeasureDensity μ x ^ 2 ≤
      (4 * (2 * Real.pi)⁻¹) * ∫ r in {r : ℝ | (2 : ℝ) ^ n < |r|}, ‖charFun μ r‖ ^ 2 := by
  have h := integral_canonical_density_level_le_fourier_tail μ
    ((memLp_measureFourier_iff μ).mpr hμ) n
  rw [integral_measureFourier_tail_eq, ← mul_assoc] at h
  exact h

end FalconerThetaGauge
