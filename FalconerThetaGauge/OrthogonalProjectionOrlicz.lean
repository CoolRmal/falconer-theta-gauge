module

public import FalconerThetaGauge.OrthogonalProjectionTail
public import FalconerThetaGauge.OrliczDualityLayers

/-!
# Logarithmic tails of the actual orthogonal densities

The concrete low-pass threshold and the literal logarithmic layer weights
are combined using nonnegative integration. All density and Fourier tails
refer to the original measure and its Radon–Nikodym density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerThetaGauge

theorem integral_canonicalMeasureDensity_sq_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : MemLp (charFun μ) 2 volume) :
    ∫ x, canonicalMeasureDensity μ x ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ r, ‖charFun μ r‖ ^ 2 := by
  let hF := (memLp_measureFourier_iff μ).mpr hμ
  calc
    _ = ∫ x, ‖measureFourierDensity μ hF x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [rnDeriv_ae_eq_measureFourierDensity μ hF] with x hx
      rw [← hx]
      simp only [canonicalMeasureDensity, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ‖measureFourierDensity μ hF‖ ^ 2 := integral_norm_sq_eq_Lp_norm_sq _
    _ = (eLpNorm (measureFourier μ) 2 volume).toReal ^ 2 := by rw [norm_measureFourierDensity]
    _ = ∫ ξ, ‖measureFourier μ ξ‖ ^ 2 := (integral_norm_sq_eq_eLpNorm_two_sq hF).symm
    _ = _ := integral_norm_sq_measureFourier μ

theorem lintegral_canonicalMeasureDensity_sq_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : MemLp (charFun μ) 2 volume) :
    ∫⁻ x, ENNReal.ofReal (canonicalMeasureDensity μ x ^ 2) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * ∫⁻ r, ENNReal.ofReal (‖charFun μ r‖ ^ 2) := by
  have hf : Integrable (fun x ↦ canonicalMeasureDensity μ x ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (measurable_canonicalMeasureDensity μ).aestronglyMeasurable).mp
        (memLp_canonicalMeasureDensity μ ((memLp_measureFourier_iff μ).mpr hμ))
  have hchar := (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).mp hμ
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun _ ↦ sq_nonneg _),
    integral_canonicalMeasureDensity_sq_eq μ hμ, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hchar (Eventually.of_forall fun _ ↦ sq_nonneg _)]

theorem lintegral_canonical_density_level_le_charFun_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (charFun μ) 2 volume) (n : ℕ) :
    ∫⁻ x in {x | orthogonalDensityTailThreshold n < canonicalMeasureDensity μ x},
      ENNReal.ofReal (canonicalMeasureDensity μ x ^ 2) ≤
      ENNReal.ofReal (4 * (2 * Real.pi)⁻¹) *
        ∫⁻ r in {r : ℝ | (2 : ℝ) ^ n < |r|}, ENNReal.ofReal (‖charFun μ r‖ ^ 2) := by
  have hf : Integrable (fun x ↦ canonicalMeasureDensity μ x ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (measurable_canonicalMeasureDensity μ).aestronglyMeasurable).mp
        (memLp_canonicalMeasureDensity μ ((memLp_measureFourier_iff μ).mpr hμ))
  have hchar := (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).mp hμ
  rw [← ofReal_integral_eq_lintegral_ofReal hf.restrict (Eventually.of_forall fun _ ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hchar.restrict (Eventually.of_forall fun _ ↦ sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (integral_canonical_density_level_le_charFun_tail μ hμ n)

theorem lintegral_orliczQuadratic_le_layers {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ℝ) (hf : Measurable f) (hf₀ : ∀ x, 0 ≤ f x)
    (γ B : ℝ) (hγ : 1 ≤ γ) (hB : 0 < B) :
    ∫⁻ x, orliczQuadraticENN γ (f x) ∂ν ≤ ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ) *
      ((∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν) +
        ∑' j, ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) *
          ∫⁻ x in {x | B * (2 : ℝ) ^ j < f x}, ENNReal.ofReal (f x ^ 2) ∂ν) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ) *
        (ENNReal.ofReal (f x ^ 2) * (1 + ∑' j, dyadicAmplitudeLayer γ B (f x) j)) ∂ν := by
      apply lintegral_mono
      intro x
      unfold orliczQuadraticENN orliczQuadratic
      dsimp only
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul' (show ENNReal.ofReal (f x ^ 2) ≤ ENNReal.ofReal (f x ^ 2) from le_rfl)
          (logarithmic_amplitude_layer_le γ B (f x) hγ hB (hf₀ x))
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hsplit (x : α) : ENNReal.ofReal (f x ^ 2) *
          (1 + ∑' j, dyadicAmplitudeLayer γ B (f x) j) = ENNReal.ofReal (f x ^ 2) +
            ∑' j, ENNReal.ofReal (f x ^ 2) * dyadicAmplitudeLayer γ B (f x) j := by
        rw [mul_add, mul_one, ENNReal.tsum_mul_left]
      simp_rw [hsplit]
      have hmf : Measurable (fun x ↦ ENNReal.ofReal (f x ^ 2)) := (hf.pow_const 2).ennreal_ofReal
      have hmlayer (j : ℕ) : Measurable (fun x ↦ dyadicAmplitudeLayer γ B (f x) j) := by
        change Measurable (fun x ↦ if B * (2 : ℝ) ^ j < f x then
          ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) else 0)
        exact Measurable.ite (measurableSet_lt measurable_const hf) measurable_const measurable_const
      have hmprod (j : ℕ) : AEMeasurable (fun x ↦ ENNReal.ofReal (f x ^ 2) *
          dyadicAmplitudeLayer γ B (f x) j) ν := (hmf.mul (hmlayer j)).aemeasurable
      rw [lintegral_add_left hmf, lintegral_tsum hmprod]
      congr 1
      congr 1
      apply tsum_congr
      intro j
      have hs : MeasurableSet {x | B * (2 : ℝ) ^ j < f x} := measurableSet_lt measurable_const hf
      have he : (fun x ↦ ENNReal.ofReal (f x ^ 2) * dyadicAmplitudeLayer γ B (f x) j) =
          fun x ↦ ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) *
            {x | B * (2 : ℝ) ^ j < f x}.indicator (fun x ↦ ENNReal.ofReal (f x ^ 2)) x := by
        funext x
        unfold dyadicAmplitudeLayer
        simp only [indicator_apply, mem_ofPred_eq]
        split_ifs <;> simp [mul_comm]
      rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hs]

def lineLogFourierEnergy (γ : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, ENNReal.ofReal (‖charFun μ r‖ ^ 2) *
    ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ)

theorem lintegral_charFun_sq_le_lineLogFourierEnergy (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure ℝ) :
    (∫⁻ r, ENNReal.ofReal (‖charFun μ r‖ ^ 2)) ≤ lineLogFourierEnergy γ μ := by
  apply lintegral_mono
  intro r
  dsimp only
  have hw : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (log_exp_one_add_ge_one (abs_nonneg r)) hγ)
  conv_lhs => rw [← mul_one (ENNReal.ofReal (‖charFun μ r‖ ^ 2))]
  exact mul_le_mul' le_rfl hw

theorem tsum_frequency_tails_le (γ : ℝ) (hγ : 1 ≤ γ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∑' j, ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) *
      ∫⁻ r in {r : ℝ | (2 : ℝ) ^ j < |r|}, f r) ≤
      ENNReal.ofReal (frequencyLayerLogConstant ^ γ) *
        ∫⁻ r : ℝ, f r * ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ) := by
  have hmlayer (j : ℕ) : Measurable (fun r : ℝ ↦ dyadicAmplitudeLayer γ 1 |r| j) := by
    change Measurable (fun r : ℝ ↦ if (1 : ℝ) * (2 : ℝ) ^ j < |r| then
      ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) else 0)
    exact Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
      measurable_const measurable_const
  have hmprod (j : ℕ) : AEMeasurable (fun r ↦ f r * dyadicAmplitudeLayer γ 1 |r| j) volume :=
    (hf.mul (hmlayer j)).aemeasurable
  calc
    _ = ∑' j, ∫⁻ r, f r * dyadicAmplitudeLayer γ 1 |r| j := by
      apply tsum_congr
      intro j
      have hs : MeasurableSet {r : ℝ | (2 : ℝ) ^ j < |r|} := by measurability
      have he : (fun r ↦ f r * dyadicAmplitudeLayer γ 1 |r| j) =
          fun r ↦ ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) *
            {r : ℝ | (2 : ℝ) ^ j < |r|}.indicator f r := by
        funext r
        unfold dyadicAmplitudeLayer
        simp only [one_mul, indicator_apply, mem_ofPred_eq]
        split_ifs <;> simp [mul_comm]
      rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hs]
    _ = ∫⁻ r, f r * ∑' j, dyadicAmplitudeLayer γ 1 |r| j := by
      rw [← lintegral_tsum hmprod]
      apply lintegral_congr
      intro r
      exact ENNReal.tsum_mul_left
    _ ≤ ∫⁻ r, ENNReal.ofReal (frequencyLayerLogConstant ^ γ) *
        (f r * ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ)) := by
      apply lintegral_mono
      intro r
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul' (show f r ≤ f r from le_rfl) (dyadic_frequency_layer_le γ |r| hγ (abs_nonneg r))
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

def orthogonalOrliczLineConstant (γ : ℝ) : ℝ :=
  (4 * amplitudeLogConstant (2 * (1 + orthogonalLowpassAmplitudeConstant))) ^ γ *
    ((2 * Real.pi)⁻¹ + (4 * (2 * Real.pi)⁻¹) * frequencyLayerLogConstant ^ γ)

/-- The literal quadratic Orlicz density norm is bounded by the logarithmically weighted
Fourier square energy on the line, uniformly for all Borel probabilities. -/
theorem lintegral_orliczQuadratic_canonical_le (γ : ℝ) (hγ : 1 ≤ γ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : MemLp (charFun μ) 2 volume) :
    (∫⁻ x, orliczQuadraticENN γ (canonicalMeasureDensity μ x)) ≤
      ENNReal.ofReal (orthogonalOrliczLineConstant γ) * lineLogFourierEnergy γ μ := by
  let B := 2 * (1 + orthogonalLowpassAmplitudeConstant)
  have hB : 0 < B := by dsimp [B]; linarith [orthogonalLowpassAmplitudeConstant_nonneg]
  have hA := amplitudeLogConstant_pos hB
  have hFreq : 0 < frequencyLayerLogConstant := by
    unfold frequencyLayerLogConstant
    have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have h := lintegral_orliczQuadratic_le_layers volume (canonicalMeasureDensity μ)
    (measurable_canonicalMeasureDensity μ) (canonicalMeasureDensity_nonneg μ) γ B hγ hB
  have htail : (∑' j, ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) *
      ∫⁻ x in {x | B * (2 : ℝ) ^ j < canonicalMeasureDensity μ x},
        ENNReal.ofReal (canonicalMeasureDensity μ x ^ 2)) ≤
        ENNReal.ofReal (4 * (2 * Real.pi)⁻¹) * ENNReal.ofReal (frequencyLayerLogConstant ^ γ) *
          lineLogFourierEnergy γ μ := by
    calc
      _ ≤ ∑' j, ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) *
          (ENNReal.ofReal (4 * (2 * Real.pi)⁻¹) *
            ∫⁻ r in {r : ℝ | (2 : ℝ) ^ j < |r|}, ENNReal.ofReal (‖charFun μ r‖ ^ 2)) := by
        apply ENNReal.tsum_le_tsum
        intro j
        exact mul_le_mul' le_rfl (lintegral_canonical_density_level_le_charFun_tail μ hμ j)
      _ = ENNReal.ofReal (4 * (2 * Real.pi)⁻¹) *
          ∑' j, ENNReal.ofReal (dyadicAmplitudeLayerWeight γ j) *
            ∫⁻ r in {r : ℝ | (2 : ℝ) ^ j < |r|}, ENNReal.ofReal (‖charFun μ r‖ ^ 2) := by
        simp_rw [mul_left_comm (ENNReal.ofReal (dyadicAmplitudeLayerWeight γ _))]
        rw [ENNReal.tsum_mul_left]
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl (tsum_frequency_tails_le γ hγ _ (by fun_prop))
  refine h.trans ?_
  rw [lintegral_canonicalMeasureDensity_sq_eq μ hμ]
  calc
    _ ≤ ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ) *
        (ENNReal.ofReal ((2 * Real.pi)⁻¹) * lineLogFourierEnergy γ μ +
          ENNReal.ofReal (4 * (2 * Real.pi)⁻¹) * ENNReal.ofReal (frequencyLayerLogConstant ^ γ) *
            lineLogFourierEnergy γ μ) := by
      exact mul_le_mul' le_rfl (add_le_add
        (mul_le_mul' le_rfl (lintegral_charFun_sq_le_lineLogFourierEnergy γ (zero_le_one.trans hγ) μ)) htail)
    _ = _ := by
      have hcoeff : ENNReal.ofReal (orthogonalOrliczLineConstant γ) =
          ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ) *
            (ENNReal.ofReal ((2 * Real.pi)⁻¹) +
              ENNReal.ofReal (4 * (2 * Real.pi)⁻¹) * ENNReal.ofReal (frequencyLayerLogConstant ^ γ)) := by
        change ENNReal.ofReal ((4 * amplitudeLogConstant B) ^ γ *
          ((2 * Real.pi)⁻¹ + (4 * (2 * Real.pi)⁻¹) * frequencyLayerLogConstant ^ γ)) = _
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [hcoeff]
      ring

end FalconerThetaGauge
