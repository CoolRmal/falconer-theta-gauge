module

public import FalconerThetaGauge.OrliczEnergyFourier
public import FalconerThetaGauge.RadialProjectionPolar
public import FalconerThetaGauge.OrthogonalProjectionFourierDensity

/-!
# Orthogonal Fourier slices at the logarithmic endpoint

The projection is the actual inner-product pushforward. Polar coordinates
give its averaged weighted Fourier energy, and reflection yields square
integrability on almost every full line. No power Frostman exponent is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

def orthogonalProjection (v x : Plane) : ℝ := ⟪x, v⟫

def orthogonalProjectionMeasure (μ : Measure Plane) (v : Plane) : Measure ℝ :=
  μ.map (orthogonalProjection v)

@[fun_prop]
theorem continuous_orthogonalProjection (v : Plane) : Continuous (orthogonalProjection v) := by
  unfold orthogonalProjection
  fun_prop

instance orthogonalProjectionMeasure.instIsProbabilityMeasure (μ : Measure Plane)
    [IsProbabilityMeasure μ] (v : Plane) : IsProbabilityMeasure (orthogonalProjectionMeasure μ v) := by
  unfold orthogonalProjectionMeasure
  infer_instance

theorem charFun_orthogonalProjection (μ : Measure Plane) [IsFiniteMeasure μ]
    (v : Plane) (r : ℝ) :
    charFun (orthogonalProjectionMeasure μ v) r = charFun μ (r • v) := by
  rw [orthogonalProjectionMeasure, charFun_apply, integral_map (by fun_prop) (by fun_prop),
    charFun_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    simp only [orthogonalProjection, real_inner_comm, real_inner_smul_right,
      RCLike.inner_apply, conj_trivial, mul_comm]

theorem lintegral_angular_weighted_positive_fourier_eq (γ : ℝ) (μ : Measure Plane)
    [IsFiniteMeasure μ] :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + r)) ^ γ) = logarithmicFourierEnergy γ μ := by
  have hm : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (‖charFun μ (p.1 • angularDirection p.2)‖ ^ 2) *
        ENNReal.ofReal ((Real.log (Real.exp 1 + p.1)) ^ γ)) := by
    fun_prop
  rw [← setLIntegral_prod_symm _ hm.aemeasurable, logarithmicFourierEnergy,
    ← lintegral_polar_euclidean]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  have hr : 0 < p.1 := hp.1
  simp only [logarithmicFourierWeight, norm_planarMeasureFourier, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, norm_angularDirection, mul_one]
  have hc := ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
  symm
  calc
    _ = (ENNReal.ofReal p.1 * (ENNReal.ofReal p.1)⁻¹) *
        (ENNReal.ofReal (‖charFun μ (p.1 • angularDirection p.2)‖ ^ 2) *
          ENNReal.ofReal ((Real.log (Real.exp 1 + p.1)) ^ γ)) := by
      ac_rfl
    _ = _ := by rw [hc, one_mul]

theorem lintegral_angular_positive_fourier_le (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure Plane)
    [IsFiniteMeasure μ] :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) ≤ logarithmicFourierEnergy γ μ := by
  rw [← lintegral_angular_weighted_positive_fourier_eq]
  apply lintegral_mono
  intro θ
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hlog : 1 ≤ Real.log (Real.exp 1 + r) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + r from le_add_of_nonneg_right hr.le)
    simpa only [Real.log_exp] using h
  have hw : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((Real.log (Real.exp 1 + r)) ^ γ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hlog hγ)
  conv_lhs => rw [← mul_one (ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2))]
  exact mul_le_mul' le_rfl hw

theorem lintegral_Iio_eq_Ioi_of_even {f : ℝ → ℝ≥0∞} (hf : ∀ x, f (-x) = f x) :
    ∫⁻ r in Iio (0 : ℝ), f r = ∫⁻ r in Ioi (0 : ℝ), f r := by
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Iio (0 : ℝ)) measurableSet_Iio).lintegral_comp_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding f
  have hset : (Neg.neg ⁻¹' Iio (0 : ℝ)) = Ioi 0 := by ext x; simp
  simpa only [hf, hset] using h.symm

theorem lintegral_lt_top_of_even_of_Ioi {f : ℝ → ℝ≥0∞} (hf : ∀ x, f (-x) = f x)
    (hpos : ∫⁻ r in Ioi (0 : ℝ), f r < ∞) : ∫⁻ r, f r < ∞ := by
  have hneg := lintegral_Iio_eq_Ioi_of_even hf
  rw [← lintegral_add_compl f measurableSet_Ioi, compl_Ioi,
    ← setLIntegral_congr Iio_ae_eq_Iic, hneg]
  exact ENNReal.add_lt_top.mpr ⟨hpos, hpos⟩

theorem ae_memLp_charFun_orthogonalProjection (γ : ℝ) (hγ : 0 ≤ γ)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (henergy : logarithmicFourierEnergy γ μ ≠ ∞) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      MemLp (charFun (orthogonalProjectionMeasure μ (angularDirection θ))) 2 volume := by
  have hfin := lt_of_le_of_lt (lintegral_angular_positive_fourier_le γ hγ μ)
    (lt_top_iff_ne_top.mpr henergy)
  have hm : Measurable (fun θ : ℝ ↦ ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2)) := by fun_prop
  filter_upwards [ae_lt_top hm hfin.ne] with θ hθ
  change MemLp (fun r ↦ charFun (orthogonalProjectionMeasure μ (angularDirection θ)) r) 2 volume
  simp_rw [charFun_orthogonalProjection]
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) (by fun_prop)]
  have heven (r : ℝ) : ENNReal.ofReal (‖charFun μ ((-r) • angularDirection θ)‖ ^ 2) =
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) := by
    simp only [neg_smul, charFun_neg, RCLike.norm_conj]
  have h := lintegral_lt_top_of_even_of_Ioi heven hθ
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

theorem ae_memLp_charFun_orthogonalProjection_circle (γ : ℝ) (hγ : 0 ≤ γ)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (henergy : logarithmicFourierEnergy γ μ ≠ ∞) :
    ∀ᵐ (w : UnitCircle) ∂circleArcLength,
      MemLp (charFun (orthogonalProjectionMeasure μ (w : Plane))) 2 volume := by
  have hm : Measurable (fun w : UnitCircle ↦ ∫⁻ r : ℝ,
      ENNReal.ofReal (‖charFun μ (r • (w : Plane))‖ ^ 2)) := by fun_prop
  have hangle : ∀ᵐ θ ∂radialAngularMeasure, ∫⁻ r : ℝ,
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) < ∞ := by
    rw [radialAngularMeasure, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_memLp_charFun_orthogonalProjection γ hγ μ henergy] with θ hθ
    change MemLp (fun r ↦ charFun (orthogonalProjectionMeasure μ (angularDirection θ)) r)
      2 volume at hθ
    simp_rw [charFun_orthogonalProjection] at hθ
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        hθ.aestronglyMeasurable).mp hθ.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h
  have hcircle : ∀ᵐ (w : UnitCircle) ∂circleArcLength, ∫⁻ r : ℝ,
      ENNReal.ofReal (‖charFun μ (r • (w : Plane))‖ ^ 2) < ∞ := by
    rw [circleArcLength, ae_map_iff continuous_unitCircleOfAngle.measurable.aemeasurable
      (measurableSet_lt hm measurable_const)]
    exact hangle
  filter_upwards [hcircle] with w hw
  change MemLp (fun r ↦ charFun (orthogonalProjectionMeasure μ (w : Plane)) r) 2 volume
  simp_rw [charFun_orthogonalProjection]
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) (by fun_prop)]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using hw

end FalconerThetaGauge
