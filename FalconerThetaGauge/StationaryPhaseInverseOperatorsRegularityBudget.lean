/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.StationaryPhaseInverseOperatorsRegularity
public import FalconerThetaGauge.StationaryPhaseInverseOperatorBudget

/-! # The actual numerical derivative costs of the inverse operators -/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace FalconerThetaGauge

theorem stationaryPhaseInverseOperator_isDerivativeRegular_budget {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) :
    IsDerivativeRegular (A * (800 * j * M ^ 2) ^ j) M K
      (stationaryPhaseInverseOperator j G) :=
  (stationaryPhaseInverseOperator_isDerivativeRegular hG).mono_amplitude
    (mul_le_mul_of_nonneg_left
      (stationaryPhaseInversePolynomial_weightedNorm_le hG.one_le_scale) hG.amplitude_nonneg)

theorem stationaryPhaseConjugateInverseOperator_isDerivativeRegular_budget {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G) :
    IsDerivativeRegular (A * (800 * j * M ^ 2) ^ j) M K
      (stationaryPhaseConjugateInverseOperator j G) :=
  (stationaryPhaseConjugateInverseOperator_isDerivativeRegular hG).mono_amplitude
    (mul_le_mul_of_nonneg_left
      (stationaryPhaseInversePolynomial_weightedNorm_le hG.one_le_scale) hG.amplitude_nonneg)

theorem stationaryPhaseInverseOperator_isDerivativeRegular_uniform {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G)
    (N : ℕ) (hj : j ≤ N) :
    IsDerivativeRegular (A * (200 * N * M ^ 2) ^ j) M K
      (stationaryPhaseInverseOperator j G) :=
  (stationaryPhaseInverseOperator_isDerivativeRegular hG).mono_amplitude
    (mul_le_mul_of_nonneg_left
      (stationaryPhaseInversePolynomial_weightedNorm_uniform hG.one_le_scale N hj)
      hG.amplitude_nonneg)

theorem stationaryPhaseConjugateInverseOperator_isDerivativeRegular_uniform {G : ℝ → ℂ}
    {A M : ℝ} {K j : ℕ} (hG : IsDerivativeRegular A M (K + 2 * j) G)
    (N : ℕ) (hj : j ≤ N) :
    IsDerivativeRegular (A * (200 * N * M ^ 2) ^ j) M K
      (stationaryPhaseConjugateInverseOperator j G) :=
  (stationaryPhaseConjugateInverseOperator_isDerivativeRegular hG).mono_amplitude
    (mul_le_mul_of_nonneg_left
      (stationaryPhaseInversePolynomial_weightedNorm_uniform hG.one_le_scale N hj)
      hG.amplitude_nonneg)

end FalconerThetaGauge
