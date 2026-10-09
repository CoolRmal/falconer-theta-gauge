module

public import FalconerThetaGauge.OrliczEnergyFourierGaussian
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Integrability at the planar Fourier origin

The inverse norm is locally integrable in the plane, with its extended value
infinite at the origin. Its difference from the real inverse occurs at a
Lebesgue-null singleton. This controls the low-frequency part of the actual
logarithmically weighted Fourier energy of a probability measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerThetaGauge

/-- The actual extended inverse norm has a finite integral over every bounded planar ball. -/
theorem lintegral_inv_norm_ball_ne_top (r : ℝ) :
    (∫⁻ ξ : Plane in Metric.ball 0 r, (ENNReal.ofReal ‖ξ‖)⁻¹) ≠ ∞ := by
  have hint : IntegrableOn (fun ξ : Plane ↦ ‖ξ‖⁻¹) (Metric.ball 0 r) volume := by
    refine integrableOn_ball_of_norm_le_rpow (by simp [Plane]) (C := 1) (α := 1)
      (by simp [Plane]) ?_ ?_
    · exact Eventually.of_forall fun ξ ↦ by
        simp [Real.rpow_neg_one]
    · fun_prop
  have hfinite : (∫⁻ ξ : Plane in Metric.ball 0 r, ENNReal.ofReal ‖ξ‖⁻¹) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ ↦
      inv_nonneg.mpr (norm_nonneg ξ))).mp hint.hasFiniteIntegral
  have heq : (∫⁻ ξ : Plane in Metric.ball 0 r, (ENNReal.ofReal ‖ξ‖)⁻¹) =
      ∫⁻ ξ : Plane in Metric.ball 0 r, ENNReal.ofReal ‖ξ‖⁻¹ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne (volume : Measure Plane) 0)] with ξ hξ
    exact (ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hξ)).symm
  rw [heq]
  exact hfinite.ne

/-- The true logarithmic Fourier integrand has a finite low-frequency integral. -/
theorem lintegral_low_frequency_log_fourier_ne_top (μ : Measure Plane)
    [IsProbabilityMeasure μ] {γ : ℝ} (hγ : 0 ≤ γ) :
    (∫⁻ ξ : Plane in Metric.ball 0 1,
      ENNReal.ofReal (Real.log (2 + ‖ξ‖) ^ γ * ‖planarMeasureFourier μ ξ‖ ^ 2) *
        (ENNReal.ofReal ‖ξ‖)⁻¹) ≠ ∞ := by
  have hbound : (∫⁻ ξ : Plane in Metric.ball 0 1,
      ENNReal.ofReal (Real.log (2 + ‖ξ‖) ^ γ * ‖planarMeasureFourier μ ξ‖ ^ 2) *
        (ENNReal.ofReal ‖ξ‖)⁻¹) ≤
      ENNReal.ofReal (Real.log 3 ^ γ) *
        ∫⁻ ξ : Plane in Metric.ball 0 1, (ENNReal.ofReal ‖ξ‖)⁻¹ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with ξ hξ
    have hξ1 : ‖ξ‖ < 1 := by simpa using Metric.mem_ball.mp hξ
    have hlog : Real.log (2 + ‖ξ‖) ≤ Real.log 3 :=
      Real.log_le_log (by positivity) (by linarith)
    have hweight : Real.log (2 + ‖ξ‖) ^ γ ≤ Real.log 3 ^ γ :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith [norm_nonneg ξ])) hlog hγ
    have hchar : ‖planarMeasureFourier μ ξ‖ ^ 2 ≤ 1 := by
      rw [norm_planarMeasureFourier]
      nlinarith [norm_charFun_le_one (μ := μ) ξ, norm_nonneg (charFun μ ξ)]
    have hproduct : Real.log (2 + ‖ξ‖) ^ γ * ‖planarMeasureFourier μ ξ‖ ^ 2 ≤
        Real.log 3 ^ γ := by
      calc
        _ ≤ Real.log (2 + ‖ξ‖) ^ γ * 1 :=
          mul_le_mul_of_nonneg_left hchar
            (Real.rpow_nonneg (Real.log_nonneg (by linarith [norm_nonneg ξ])) γ)
        _ ≤ _ := by simpa using hweight
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hproduct) _
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_inv_norm_ball_ne_top 1)) hbound

end FalconerThetaGauge
