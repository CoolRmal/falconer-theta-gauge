module

public import FalconerThetaGauge.OrliczEnergyFourierWeight
public import FalconerThetaGauge.OrliczEnergyFourierLow

/-!
# The critical logarithmic Fourier energy estimate

This is the manuscript's Lemma 5.2: the Fourier energy with the literal weight
`log(exp(1) + ‖ξ‖)^γ / ‖ξ‖` is bounded by a constant depending only on γ times
one plus the critical logarithmic spatial energy. The origin and diagonal use
extended nonnegative inverses, and finiteness is proved rather than stipulated.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

def logarithmicFourierLowConstant (γ : ℝ) : ℝ :=
  (Real.log (Real.exp 1 + 1)) ^ γ *
    (∫⁻ ξ : Plane in Metric.ball 0 1, (ENNReal.ofReal ‖ξ‖)⁻¹).toReal

theorem logarithmicFourierLowConstant_nonneg (γ : ℝ) :
    0 ≤ logarithmicFourierLowConstant γ := by
  unfold logarithmicFourierLowConstant
  have hlog : 0 ≤ Real.log (Real.exp 1 + 1) :=
    (Real.log_pos (by linarith [Real.exp_pos 1])).le
  exact mul_nonneg (Real.rpow_nonneg hlog γ) ENNReal.toReal_nonneg

def logarithmicFourierEnergyConstant (γ : ℝ) : ℝ :=
  logarithmicFourierLowConstant γ + logarithmicFourierComparisonConstant γ *
    (4 * Real.pi * dyadicGaussianEnergyConstant γ) + 1

theorem logarithmicFourierEnergyConstant_pos (γ : ℝ) :
    0 < logarithmicFourierEnergyConstant γ := by
  unfold logarithmicFourierEnergyConstant
  have hh : 0 < logarithmicFourierComparisonConstant γ *
      (4 * Real.pi * dyadicGaussianEnergyConstant γ) := by
    exact mul_pos (logarithmicFourierComparisonConstant_pos γ)
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (dyadicGaussianEnergyConstant_pos γ))
  linarith [logarithmicFourierLowConstant_nonneg γ]

theorem lintegral_fourier_low_le (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] :
    ∫⁻ ξ : Plane in Metric.ball 0 1, ENNReal.ofReal (‖planarMeasureFourier μ ξ‖ ^ 2) *
        logarithmicFourierWeight γ ξ ≤ ENNReal.ofReal (logarithmicFourierLowConstant γ) := by
  have hl : 0 ≤ (Real.log (Real.exp 1 + 1)) ^ γ := by
    apply Real.rpow_nonneg
    exact (Real.log_pos (by linarith [Real.exp_pos 1])).le
  rw [logarithmicFourierLowConstant, ENNReal.ofReal_mul hl,
    ENNReal.ofReal_toReal (lintegral_inv_norm_ball_ne_top 1)]
  exact lintegral_fourier_low_le_inverse_norm γ hγ μ

/-- Lemma 5.2, with one uniform finite positive constant for every planar probability. -/
theorem logarithmicFourierEnergy_le (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] :
    logarithmicFourierEnergy γ μ ≤ ENNReal.ofReal (logarithmicFourierEnergyConstant γ) *
      (1 + logCriticalEnergy γ μ) := by
  have hcompl : (Metric.ball (0 : Plane) 1)ᶜ = {ξ : Plane | 1 ≤ ‖ξ‖} := by
    ext ξ
    simp only [mem_compl_iff, Metric.mem_ball, dist_zero_right, mem_ofPred_eq, not_lt]
  rw [logarithmicFourierEnergy, ← lintegral_add_compl _ Metric.isOpen_ball.measurableSet,
    hcompl]
  have hhigh : 0 ≤ logarithmicFourierComparisonConstant γ *
      (4 * Real.pi * dyadicGaussianEnergyConstant γ) := by
    exact (mul_pos (logarithmicFourierComparisonConstant_pos γ)
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (dyadicGaussianEnergyConstant_pos γ))).le
  have hmono : ENNReal.ofReal (logarithmicFourierLowConstant γ) ≤
      ENNReal.ofReal (logarithmicFourierLowConstant γ) * (1 + logCriticalEnergy γ μ) := by
    conv_lhs => rw [← mul_one (ENNReal.ofReal (logarithmicFourierLowConstant γ))]
    exact mul_le_mul' le_rfl (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ ENNReal.ofReal (logarithmicFourierLowConstant γ) +
        ENNReal.ofReal (logarithmicFourierComparisonConstant γ *
          (4 * Real.pi * dyadicGaussianEnergyConstant γ)) * (1 + logCriticalEnergy γ μ) :=
      add_le_add (lintegral_fourier_low_le γ hγ μ) (lintegral_fourier_high_le γ hγ μ)
    _ ≤ ENNReal.ofReal (logarithmicFourierLowConstant γ) * (1 + logCriticalEnergy γ μ) +
        ENNReal.ofReal (logarithmicFourierComparisonConstant γ *
          (4 * Real.pi * dyadicGaussianEnergyConstant γ)) * (1 + logCriticalEnergy γ μ) :=
      add_le_add hmono le_rfl
    _ = ENNReal.ofReal (logarithmicFourierLowConstant γ +
        logarithmicFourierComparisonConstant γ * (4 * Real.pi * dyadicGaussianEnergyConstant γ)) *
          (1 + logCriticalEnergy γ μ) := by
      rw [← add_mul, ENNReal.ofReal_add (logarithmicFourierLowConstant_nonneg γ) hhigh]
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      unfold logarithmicFourierEnergyConstant
      linarith

/-- Finite critical logarithmic spatial energy implies finite literal Fourier energy. -/
theorem logarithmicFourierEnergy_ne_top (γ : ℝ) (hγ : 0 ≤ γ) (μ : Measure Plane)
    [IsProbabilityMeasure μ] (henergy : logCriticalEnergy γ μ ≠ ∞) :
    logarithmicFourierEnergy γ μ ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness) (logarithmicFourierEnergy_le γ hγ μ)

end FalconerThetaGauge
