module

public import FalconerThetaGauge.StationaryCircularPreparedArc

/-! # The literal one-sided circular expansion with the actual prepared cutoff -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem preparedAngularAmplitude_isDerivativeRegular {T : ℕ} (hT : 1 ≤ T)
    (α : ℝ) {H : ℝ → ℂ} {A M : ℝ} (hH : IsDerivativeRegular A M (4 * T) H) :
    IsDerivativeRegular A (1200 * (T : ℝ) ^ 2 + M) (4 * T)
      (preparedAngularAmplitude (6 * T) α H) := by
  have h := ((preparedAngularCutoff_isDerivativeRegular hT α).of_le
    (by omega : 4 * T ≤ 6 * T)).mul hH
  simpa only [one_mul, preparedAngularAmplitude] using h

theorem contDiff_preparedAngularAmplitude (K : ℕ) (α : ℝ) {H : ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (preparedAngularAmplitude K α H) :=
  (contDiff_preparedAngularCutoff K α).mul hH

theorem periodic_preparedAngularAmplitude (K : ℕ) (α : ℝ) {H : ℝ → ℂ}
    (hH : Periodic H (2 * Real.pi)) :
    Periodic (preparedAngularAmplitude K α H) (2 * Real.pi) := by
  intro φ
  change preparedAngularCutoff K α (φ + 2 * Real.pi) * H (φ + 2 * Real.pi) = _
  rw [periodic_preparedAngularCutoff K α, hH]
  rfl

/-- Actual multiplication by `ψ` supplies localization, equality of every positive
operator with its original action, and vanishing of every opposite operator. -/
theorem circular_stationary_phase_prepared_arc {T : ℕ} (hT : 1 ≤ T)
    {H : ℝ → ℂ} {A M α φ Λ : ℝ} (hH : IsDerivativeRegular A M (4 * T) H)
    (hHsmooth : ContDiff ℝ ∞ H) (hHP : Periodic H (2 * Real.pi)) (hΛ : 1 ≤ Λ)
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) (u : ℝ) :
    ‖(∫ t in u..u + 2 * Real.pi,
      Complex.exp (-((Λ * Real.cos (t - φ) : ℝ) : ℂ) * Complex.I) *
        preparedAngularAmplitude (6 * T) α H t) -
      (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
        (Complex.exp (-((Λ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * stationaryPhaseOperator j H φ)‖ ≤
      A * Real.sqrt (2 * Real.pi / Λ) *
        circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
          (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / Λ) ^ T := by
  have hreg := preparedAngularAmplitude_isDerivativeRegular hT α hH
  have h := circular_stationary_phase (hreg.of_le (by omega : 2 * T + 2 ≤ 4 * T))
    (contDiff_preparedAngularAmplitude _ _ hHsmooth)
    (periodic_preparedAngularAmplitude _ _ hHP) hΛ u (φ := φ)
  have hpositive (j : ℕ) :
      stationaryPhaseOperator j (preparedAngularAmplitude (6 * T) α H) φ =
        stationaryPhaseOperator j H φ :=
    stationaryPhaseOperator_preparedAngularAmplitude _ _ _ _ hφ
  have hopposite (j : ℕ) :
      stationaryPhaseConjugateOperator j (preparedAngularAmplitude (6 * T) α H)
        (φ + Real.pi) = 0 :=
    stationaryPhaseConjugateOperator_preparedAngularAmplitude_eq_zero _ _ _ _ hφ
  simp_rw [hpositive, hopposite] at h
  simpa only [mul_zero, sum_const_zero, add_zero] using h

end FalconerThetaGauge
