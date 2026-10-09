module

public import FalconerThetaGauge.OrthogonalProjectionDensity
public import FalconerThetaGauge.FourierReconstructionPairing

/-!
# Concrete low-pass approximants of the orthogonal densities

The inverse square-integrable Fourier approximant is identified with the actual
Schwartz kernel convolved against the source measure. Its pointwise bound is
therefore a consequence of probability mass, as required in Lemma 5.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter SchwartzMap FourierTransform
open scoped ENNReal ContDiff

namespace FalconerThetaGauge

def measureLowpassFourier (μ : Measure ℝ) (n : ℕ) (ξ : ℝ) : ℂ :=
  measureFourier μ ξ * (𝓕 (reconstructionLowpass n)) ξ

theorem memLp_measureLowpassFourier (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    MemLp (measureLowpassFourier μ n) 2 volume := by
  apply (((𝓕 (reconstructionLowpass n)).memLp 2 volume).norm.const_mul (μ.real Set.univ)).mono'
    ((continuous_measureFourier μ).mul (𝓕 (reconstructionLowpass n)).continuous).aestronglyMeasurable
  exact Eventually.of_forall fun ξ ↦ by
    change ‖measureFourier μ ξ * (𝓕 (reconstructionLowpass n)) ξ‖ ≤ _
    rw [norm_mul, measureFourier_eq_charFun]
    exact mul_le_mul_of_nonneg_right (norm_charFun_le _) (norm_nonneg _)

def measureLowpassFrequencyL2 (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_measureLowpassFourier μ n).toLp (measureLowpassFourier μ n)

def measureLowpassDensityL2 (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕⁻ (measureLowpassFrequencyL2 μ n)

theorem integral_measureLowpassDensityL2_mul_schwartz (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    ∫ x, φ x * measureLowpassDensityL2 μ n x =
      ∫ x, schwartzMeasureDensity μ (reconstructionLowpass n) x * φ x := by
  have h := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T φ)
    (Lp.fourierInv_toTemperedDistribution_eq (measureLowpassFrequencyL2 μ n))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at h
  rw [integral_schwartzMeasureDensity_mul_schwartz]
  unfold measureLowpassDensityL2
  rw [← h]
  apply integral_congr_ae
  filter_upwards [(memLp_measureLowpassFourier μ n).coeFn_toLp] with ξ hξ
  rw [show measureLowpassFrequencyL2 μ n ξ = measureLowpassFourier μ n ξ from hξ]
  unfold measureLowpassFourier
  ring

theorem measureLowpassDensityL2_ae_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    measureLowpassDensityL2 μ n =ᵐ[volume] schwartzMeasureDensity μ (reconstructionLowpass n) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (measureLowpassDensityL2 μ n)).locallyIntegrable (by norm_num))
    (integrable_schwartzMeasureDensity μ (reconstructionLowpass n)).locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have h := integral_measureLowpassDensityL2_mul_schwartz μ n (hc'.toSchwartzMap hg')
  convert h using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x <;>
    simp [RCLike.real_smul_eq_coe_mul, mul_comm]

def orthogonalLowpassAmplitudeConstant : ℝ := SchwartzMap.seminorm ℝ 0 0 reconstructionKernel /
  (2 * Real.pi)

theorem orthogonalLowpassAmplitudeConstant_nonneg : 0 ≤ orthogonalLowpassAmplitudeConstant := by
  unfold orthogonalLowpassAmplitudeConstant
  positivity

theorem norm_schwartzMeasureDensity_lowpass_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (x : ℝ) :
    ‖schwartzMeasureDensity μ (reconstructionLowpass n) x‖ ≤
      orthogonalLowpassAmplitudeConstant * (2 : ℝ) ^ n := by
  have hpoint (z : ℝ) : ‖reconstructionLowpass n (x - z)‖ ≤
      reconstructionScale n * SchwartzMap.seminorm ℝ 0 0 reconstructionKernel := by
    rw [reconstructionLowpass, dilatedReconstructionKernel_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (reconstructionScale_pos n)]
    exact mul_le_mul_of_nonneg_left (reconstructionKernel.norm_le_seminorm ℝ _)
      (reconstructionScale_pos n).le
  have h := norm_integral_le_of_norm_le (μ := μ)
    (integrable_const (reconstructionScale n * SchwartzMap.seminorm ℝ 0 0 reconstructionKernel))
    (Eventually.of_forall hpoint)
  have hs : reconstructionScale n * SchwartzMap.seminorm ℝ 0 0 reconstructionKernel =
      orthogonalLowpassAmplitudeConstant * (2 : ℝ) ^ n := by
    unfold reconstructionScale orthogonalLowpassAmplitudeConstant
    ring
  simpa [schwartzMeasureDensity, hs] using h

end FalconerThetaGauge
