module

public import FalconerThetaGauge.StationaryCircularInversion

/-! # Error estimates for the actual circular inverse series -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_inverse_real_complex {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ‖(Λ : ℂ)⁻¹‖ = Λ⁻¹ := by
  simp [Complex.norm_real, abs_of_nonneg hΛ]

theorem norm_preparedInverseCircleSeries_sub_le {T : ℕ} (hT : 0 < T)
    (α : ℝ) {B : ℝ → ℂ} (hBs : ContDiff ℝ ∞ B) (φ Λ u : ℝ) :
    ‖preparedInverseCircleSeries T α B φ Λ u - preparedCirclePhaseFactor Λ * B φ‖ ≤
      Real.sqrt (2 * Real.pi / Λ) *
        ‖stationaryPhaseFiniteTail T (Λ : ℂ)⁻¹ B φ‖ +
          ∑ j ∈ range T, ‖(Λ : ℂ)⁻¹‖ ^ j *
            ‖preparedInverseCircleError T α B φ Λ u j‖ := by
  rw [preparedInverseCircleSeries_sub_eq hT α hBs]
  calc
    _ ≤ ‖preparedCirclePhaseFactor Λ * stationaryPhaseFiniteTail T (Λ : ℂ)⁻¹ B φ‖ +
        ‖∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j *
          preparedInverseCircleError T α B φ Λ u j‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_preparedCirclePhaseFactor]
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ j ∈ range T,
            ‖(Λ : ℂ)⁻¹ ^ j * preparedInverseCircleError T α B φ Λ u j‖ :=
          norm_sum_le _ _
        _ = _ := by simp only [norm_mul, norm_pow]

/-- The estimate uses the actual finite inversion tail and the actual one-sided
stationary errors for every inverse amplitude. -/
theorem preparedInverseCircleSeries_approximation_sum {T : ℕ} (hT : 1 ≤ T)
    {B : ℝ → ℂ} {A M α φ Λ : ℝ} (hB : IsDerivativeRegular A M (6 * T) B)
    (hBs : ContDiff ℝ ∞ B) (hBP : Periodic B (2 * Real.pi)) (hΛ : 1 ≤ Λ)
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) (u : ℝ)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2)
    (hscale : 800 * (2 * T) * M ^ 2 * Λ⁻¹ ≤ q) :
    ‖preparedInverseCircleSeries T α B φ Λ u - preparedCirclePhaseFactor Λ * B φ‖ ≤
      Real.sqrt (2 * Real.pi / Λ) * (2 * A * (2 * T + 1) * q ^ T) +
        ∑ j ∈ range T, Λ⁻¹ ^ j * ((A * (200 * T * M ^ 2) ^ j) *
          Real.sqrt (2 * Real.pi / Λ) *
            circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
              (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / Λ) ^ T) := by
  have hΛ₀ : 0 ≤ Λ := by linarith
  have htail := norm_stationaryPhaseFiniteTail_le_geometric hBs (by omega : 0 < T)
    (hB.of_le (by omega : 4 * T ≤ 6 * T)) (Λ : ℂ)⁻¹ φ hq₀ hq₁
    (by simpa only [norm_inverse_real_complex hΛ₀] using hscale)
  calc
    _ ≤ Real.sqrt (2 * Real.pi / Λ) *
        ‖stationaryPhaseFiniteTail T (Λ : ℂ)⁻¹ B φ‖ +
          ∑ j ∈ range T, Λ⁻¹ ^ j *
            ‖preparedInverseCircleError T α B φ Λ u j‖ := by
      simpa only [norm_inverse_real_complex hΛ₀] using
        norm_preparedInverseCircleSeries_sub_le (by omega) α hBs φ Λ u
    _ ≤ _ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _)
      · apply sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (norm_preparedInverseCircleError_le hT hB hBs hBP hΛ hφ u hj) (by positivity)

end FalconerThetaGauge
