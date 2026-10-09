module

public import FalconerThetaGauge.OrthogonalProjectionOrlicz

/-!
# The endpoint orthogonal projection theorem

This completes Lemma 5.3 with a jointly Borel family of actual projection
densities on the Euclidean unit circle and its true arc-length measure.
The average quadratic Orlicz bound follows from the proved one-dimensional
tail estimate and the exact polar-coordinate weighted Fourier identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerThetaGauge

theorem lintegral_eq_two_mul_Ioi_of_even {f : ℝ → ℝ≥0∞} (hf : ∀ x, f (-x) = f x) :
    ∫⁻ r, f r = 2 * ∫⁻ r in Ioi (0 : ℝ), f r := by
  rw [← lintegral_add_compl f measurableSet_Ioi, compl_Ioi,
    ← setLIntegral_congr Iio_ae_eq_Iic, lintegral_Iio_eq_Ioi_of_even hf, two_mul]

theorem lintegral_circle_lineLogFourierEnergy_eq (γ : ℝ) (μ : Measure Plane)
    [IsFiniteMeasure μ] :
    (∫⁻ w : UnitCircle, lineLogFourierEnergy γ (orthogonalProjectionMeasure μ (w : Plane))
      ∂circleArcLength) = 2 * logarithmicFourierEnergy γ μ := by
  simp_rw [lineLogFourierEnergy, charFun_orthogonalProjection]
  have hm : Measurable (fun w : UnitCircle ↦ ∫⁻ r : ℝ,
      ENNReal.ofReal (‖charFun μ (r • (w : Plane))‖ ^ 2) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ)) := by fun_prop
  rw [circleArcLength, lintegral_map hm continuous_unitCircleOfAngle.measurable,
    radialAngularMeasure]
  simp only [coe_unitCircleOfAngle]
  have heven (θ r : ℝ) : ENNReal.ofReal (‖charFun μ ((-r) • angularDirection θ)‖ ^ 2) *
      ENNReal.ofReal ((Real.log (Real.exp 1 + |-r|)) ^ γ) =
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ) := by
    simp only [neg_smul, charFun_neg, RCLike.norm_conj, abs_neg]
  have hfull (θ : ℝ) : (∫⁻ r : ℝ,
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ)) =
      2 * ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) *
          ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ) :=
    lintegral_eq_two_mul_Ioi_of_even (f := fun r : ℝ ↦
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ)) (heven θ)
  simp_rw [hfull]
  rw [lintegral_const_mul' _ _ (by norm_num),
    ← setLIntegral_congr Ioo_ae_eq_Ioc]
  have heq : (∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + |r|)) ^ γ)) = logarithmicFourierEnergy γ μ := by
    rw [← lintegral_angular_weighted_positive_fourier_eq]
    apply lintegral_congr
    intro θ
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [abs_of_pos hr]
  rw [heq]

theorem orthogonalProjectionDensity_ae_eq_canonical (μ : Measure Plane)
    [IsProbabilityMeasure μ] (w : UnitCircle)
    (hw : MemLp (charFun (orthogonalProjectionMeasure μ (w : Plane))) 2 volume) :
    orthogonalProjectionDensity μ w =ᵐ[volume]
      canonicalMeasureDensity (orthogonalProjectionMeasure μ (w : Plane)) := by
  have hac := absolutelyContinuous_of_memLp_charFun (orthogonalProjectionMeasure μ (w : Plane)) hw
  have h := kernelDensity_ae_eq_rnDeriv (orthogonalProjectionKernel μ) volume (a := w) hac
  filter_upwards [h] with t ht
  simpa only [orthogonalProjectionKernel_apply, orthogonalProjectionDensity,
    canonicalMeasureDensity] using ht

theorem orthogonalOrliczLineConstant_pos (γ : ℝ) : 0 < orthogonalOrliczLineConstant γ := by
  have hB : 0 < 2 * (1 + orthogonalLowpassAmplitudeConstant) := by
    linarith [orthogonalLowpassAmplitudeConstant_nonneg]
  have hA := amplitudeLogConstant_pos hB
  have hFreq : 0 < frequencyLayerLogConstant := by
    unfold frequencyLayerLogConstant
    have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  unfold orthogonalOrliczLineConstant
  positivity

/-- The manuscript's actual averaged quadratic Orlicz estimate (Lemma 5.3). -/
theorem lintegral_orliczQuadratic_orthogonalProjectionDensity_le (γ : ℝ) (hγ : 1 ≤ γ)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (henergy : logarithmicFourierEnergy γ μ ≠ ∞) :
    (∫⁻ w : UnitCircle, ∫⁻ t : ℝ, orliczQuadraticENN γ (orthogonalProjectionDensity μ w t)
      ∂volume ∂circleArcLength) ≤
      ENNReal.ofReal (2 * orthogonalOrliczLineConstant γ) * logarithmicFourierEnergy γ μ := by
  calc
    _ ≤ ∫⁻ w : UnitCircle, ENNReal.ofReal (orthogonalOrliczLineConstant γ) *
        lineLogFourierEnergy γ (orthogonalProjectionMeasure μ (w : Plane)) ∂circleArcLength := by
      apply lintegral_mono_ae
      filter_upwards [ae_memLp_charFun_orthogonalProjection_circle γ (zero_le_one.trans hγ)
        μ henergy] with w hw
      have hdensity : (fun t : ℝ ↦ orliczQuadraticENN γ (orthogonalProjectionDensity μ w t))
          =ᵐ[volume] (fun t : ℝ ↦ orliczQuadraticENN γ
            (canonicalMeasureDensity (orthogonalProjectionMeasure μ (w : Plane)) t)) := by
        filter_upwards [orthogonalProjectionDensity_ae_eq_canonical μ w hw] with t ht
        rw [ht]
      rw [lintegral_congr_ae hdensity]
      exact lintegral_orliczQuadratic_canonical_le γ hγ _ hw
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_circle_lineLogFourierEnergy_eq,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      ac_rfl

theorem lintegral_orliczQuadratic_orthogonalProjectionDensity_ne_top (γ : ℝ) (hγ : 1 ≤ γ)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (henergy : logarithmicFourierEnergy γ μ ≠ ∞) :
    (∫⁻ w : UnitCircle, ∫⁻ t : ℝ, orliczQuadraticENN γ (orthogonalProjectionDensity μ w t)
      ∂volume ∂circleArcLength) ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness)
    (lintegral_orliczQuadratic_orthogonalProjectionDensity_le γ hγ μ henergy)

end FalconerThetaGauge
