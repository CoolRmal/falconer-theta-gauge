module

public import FalconerThetaGauge.FourierReconstructionEnergy
public import FalconerThetaGauge.ReconstructionDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Actual square-integrable densities from finite-measure Fourier energy

This inverse-Fourier and Radon–Nikodym argument adapts the checked proof in
`FalconerPacking/FourierDensity.lean` (Yongxi Lin, Apache 2.0). Shared Fourier
integrals and test-function duality are imported from the reconstruction modules.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped ENNReal ContDiff

namespace FalconerThetaGauge

/-- The choice between probability and `2π` Fourier normalization does not affect `L²`. -/
theorem memLp_measureFourier_iff (μ : Measure ℝ) [IsFiniteMeasure μ] :
    MemLp (measureFourier μ) 2 volume ↔ MemLp (charFun μ) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_measureFourier μ).aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm continuous_charFun.aestronglyMeasurable]
  simp_rw [measureFourier_eq_charFun]
  exact integrable_comp_mul_left_iff (fun x ↦ ‖charFun μ x‖ ^ 2)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

/-- The exact normalization factor for Fourier square energy on the real line. -/
theorem integral_norm_sq_measureFourier (μ : Measure ℝ) :
    ∫ ξ, ‖measureFourier μ ξ‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ ξ, ‖charFun μ ξ‖ ^ 2 := by
  simp_rw [measureFourier_eq_charFun]
  rw [Measure.integral_comp_mul_left (fun ξ ↦ ‖charFun μ ξ‖ ^ 2) (-2 * Real.pi)]
  congr 1
  rw [abs_inv, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), abs_of_pos Real.pi_pos]
  norm_num

/-- The error-zero Schwartz pairing criterion yields absolute continuity. -/
theorem absolutelyContinuous_of_schwartz_L2_bound {μ : Measure ℝ} [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : SchwartzMap ℝ ℂ,
      ‖∫ x, φ x ∂μ‖ ≤ C * ‖φ.toLp 2 volume‖) : μ ≪ volume := by
  apply absolutelyContinuous_of_schwartz_bound_with_error
    (σ := (0 : Measure ℝ)) (by simp) hC
  simpa using hbound

/-- The Fourier `L²` norm controls every Schwartz test against the original measure. -/
theorem norm_integral_schwartz_le_measureFourier_L2
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    ‖∫ x, φ x ∂μ‖ ≤ (eLpNorm (measureFourier μ) 2 volume).toReal * ‖φ.toLp 2 volume‖ := by
  rw [integral_schwartz_eq_measureFourier]
  have h := norm_integral_mul_le_eLpNorm_two hμ ((𝓕⁻ φ).memLp 2 volume)
  have hnorm : ‖(𝓕⁻ φ).toLp 2 volume‖ = ‖φ.toLp 2 volume‖ := by
    simpa only [fourier_fourierInv_eq] using (norm_fourier_toL2_eq (𝓕⁻ φ)).symm
  simpa only [← SchwartzMap.norm_toLp, hnorm] using h

/-- The distributional Fourier transform of the measure is its actual Fourier integral. -/
theorem fourier_measure_toTemperedDistribution
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    𝓕 μ.toTemperedDistribution =
      (hμ.toLp (measureFourier μ) : TemperedDistribution ℝ ℂ) := by
  ext φ
  simp only [TemperedDistribution.fourier_apply, Measure.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  rw [← integral_measureFourier_schwartz]
  apply integral_congr_ae
  filter_upwards [hμ.coeFn_toLp] with x hx
  simp only [hx, smul_eq_mul, mul_comm]

/-- The inverse `L²` Fourier transform provides the candidate density. -/
def measureFourierDensity (μ : Measure ℝ) (hμ : MemLp (measureFourier μ) 2 volume) :
    Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ (hμ.toLp (measureFourier μ))

/-- The candidate density represents the original measure on every Schwartz test. -/
theorem measure_toTemperedDistribution_eq_fourierDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    μ.toTemperedDistribution = (measureFourierDensity μ hμ : TemperedDistribution ℝ ℂ) := by
  calc
    μ.toTemperedDistribution = 𝓕⁻ (𝓕 μ.toTemperedDistribution) :=
      (fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ (hμ.toLp (measureFourier μ) : TemperedDistribution ℝ ℂ) := by
      rw [fourier_measure_toTemperedDistribution μ hμ]
    _ = (measureFourierDensity μ hμ : TemperedDistribution ℝ ℂ) :=
      Lp.fourierInv_toTemperedDistribution_eq _

theorem integral_schwartz_eq_fourierDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    ∫ x, φ x ∂μ = ∫ x, φ x * measureFourierDensity μ hμ x := by
  have h := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T φ)
    (measure_toTemperedDistribution_eq_fourierDensity μ hμ)
  simpa only [Measure.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] using h

/-- Plancherel gives the exact norm of the candidate density. -/
theorem norm_measureFourierDensity (μ : Measure ℝ) (hμ : MemLp (measureFourier μ) 2 volume) :
    ‖measureFourierDensity μ hμ‖ = (eLpNorm (measureFourier μ) 2 volume).toReal := by
  have h := (Lp.norm_fourier_eq (𝓕⁻ (hμ.toLp (measureFourier μ)))).symm
  simpa only [measureFourierDensity, fourier_fourierInv_eq, Lp.norm_toLp] using h

/-- Square-integrability of the measure Fourier transform implies absolute continuity. -/
theorem absolutelyContinuous_of_memLp_measureFourier
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    μ ≪ volume :=
  absolutelyContinuous_of_schwartz_L2_bound ENNReal.toReal_nonneg
    (norm_integral_schwartz_le_measureFourier_L2 μ hμ)

/-- Equivalently, a finite measure with square-integrable characteristic function is
absolutely continuous. -/
theorem absolutelyContinuous_of_memLp_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (charFun μ) 2 volume) : μ ≪ volume :=
  absolutelyContinuous_of_memLp_measureFourier μ ((memLp_measureFourier_iff μ).mpr hμ)

/-- The inverse Fourier candidate agrees almost everywhere with the Radon--Nikodym density. -/
theorem rnDeriv_ae_eq_measureFourierDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    (fun x ↦ ((μ.rnDeriv volume x).toReal : ℂ)) =ᵐ[volume] measureFourierDensity μ hμ := by
  have hac := absolutelyContinuous_of_memLp_measureFourier μ hμ
  have hr : Integrable (fun x ↦ (μ.rnDeriv volume x).toReal) volume := by
    simpa only [integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := volume) (s := Set.univ)
        (measure_ne_top μ Set.univ))
  apply ae_eq_of_integral_contDiff_smul_eq hr.ofReal.locallyIntegrable
    ((Lp.memLp (measureFourierDensity μ hμ)).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have h := integral_schwartz_eq_fourierDensity μ hμ (hc'.toSchwartzMap hg')
  rw [← integral_rnDeriv_smul hac] at h
  convert h using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x <;>
    simp [RCLike.real_smul_eq_coe_mul, mul_comm]

/-- A finite measure with square-integrable Fourier transform has a nonnegative `L¹ ∩ L²`
density, with exactly the same `L²` norm in the `2π` Fourier normalization. -/
theorem exists_L2_density_of_memLp_measureFourier
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ MemLp f 2 volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      eLpNorm f 2 volume = eLpNorm (measureFourier μ) 2 volume := by
  let f : ℝ → ℝ := fun x ↦ (μ.rnDeriv volume x).toReal
  have hm : AEStronglyMeasurable f volume :=
    (Measure.measurable_rnDeriv μ volume).ennreal_toReal.aestronglyMeasurable
  have hn : ∀ᵐ x ∂volume, ‖measureFourierDensity μ hμ x‖ = ‖f x‖ := by
    filter_upwards [rnDeriv_ae_eq_measureFourierDensity μ hμ] with x hx
    rw [← hx]
    simp only [f, Complex.norm_real, Real.norm_eq_abs]
  have hf := (Lp.memLp (measureFourierDensity μ hμ)).congr_norm hm hn
  refine ⟨f, fun _ ↦ ENNReal.toReal_nonneg, ?_, hf, ?_, ?_⟩
  · simpa only [integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := volume) (s := Set.univ)
        (measure_ne_top μ Set.univ))
  · rw [← Measure.withDensity_rnDeriv_eq μ volume
      (absolutelyContinuous_of_memLp_measureFourier μ hμ)]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top μ volume] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  · rw [← eLpNorm_congr_norm_ae
      (Lp.memLp (measureFourierDensity μ hμ)).aestronglyMeasurable hm hn,
      ← Lp.enorm_def, ← ofReal_norm,
      norm_measureFourierDensity, ENNReal.ofReal_toReal hμ.eLpNorm_ne_top]

/-- The characteristic-function hypothesis yields an actual nonnegative `L²` density. -/
theorem exists_L2_density_of_memLp_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (charFun μ) 2 volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ MemLp f 2 volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      eLpNorm f 2 volume = eLpNorm (measureFourier μ) 2 volume :=
  exists_L2_density_of_memLp_measureFourier μ ((memLp_measureFourier_iff μ).mpr hμ)

/-- Express a square integral directly through the finite `L²` seminorm. -/
theorem integral_norm_sq_eq_eLpNorm_two_sq {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : MemLp f 2 volume) :
    ∫ x, ‖f x‖ ^ 2 = (eLpNorm f 2 volume).toReal ^ 2 := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖f x‖))]

/-- The usual probability normalization gives the precise Plancherel constant for the density. -/
theorem exists_L2_density_of_memLp_charFun_sq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (charFun μ) 2 volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ MemLp f 2 volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      ∫ x, f x ^ 2 = (2 * Real.pi)⁻¹ * ∫ ξ, ‖charFun μ ξ‖ ^ 2 := by
  obtain ⟨f, hf₀, hfi, hf₂, hfd, hfn⟩ := exists_L2_density_of_memLp_charFun μ hμ
  refine ⟨f, hf₀, hfi, hf₂, hfd, ?_⟩
  calc
    ∫ x, f x ^ 2 = ∫ x, ‖f x‖ ^ 2 := by simp only [Real.norm_eq_abs, sq_abs]
    _ = (eLpNorm f 2 volume).toReal ^ 2 := integral_norm_sq_eq_eLpNorm_two_sq hf₂
    _ = (eLpNorm (measureFourier μ) 2 volume).toReal ^ 2 := by rw [hfn]
    _ = ∫ ξ, ‖measureFourier μ ξ‖ ^ 2 :=
      (integral_norm_sq_eq_eLpNorm_two_sq ((memLp_measureFourier_iff μ).mpr hμ)).symm
    _ = _ := integral_norm_sq_measureFourier μ

end FalconerThetaGauge
