module

public import FalconerThetaGauge.StationaryCircularInversionBound

/-! # Geometric absorption of the actual inverse-series stationary errors -/

@[expose] public section

noncomputable section

open Finset Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem sum_inverse_stationary_amplitudes_le_two {A D L C : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hscale : L * D ≤ 1 / 2) (T : ℕ) :
    (∑ j ∈ range T, L ^ j * ((A * D ^ j) * C)) ≤ 2 * A * C := by
  calc
    _ = A * C * ∑ j ∈ range T, (L * D) ^ j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [mul_pow]
      ring
    _ ≤ A * C * 2 := mul_le_mul_of_nonneg_left
      (sum_geometric_le_two (mul_nonneg hL hD) hscale T) (mul_nonneg hA hC)
    _ = _ := by ring

theorem inverse_stationary_amplitude_scale_le_half {T : ℕ} {M Λ q : ℝ}
    (hΛ : 0 ≤ Λ) (hq : q ≤ 1 / 2)
    (hscale : 800 * (2 * T) * M ^ 2 * Λ⁻¹ ≤ q) :
    Λ⁻¹ * (200 * T * M ^ 2) ≤ 1 / 2 := by
  have hnonneg : 0 ≤ (T : ℝ) * M ^ 2 * Λ⁻¹ := by positivity
  calc
    _ ≤ 800 * (2 * T) * M ^ 2 * Λ⁻¹ := by nlinarith
    _ ≤ q := hscale
    _ ≤ 1 / 2 := hq

/-- Actual source §7.5 Step 1: the prepared inverse-operator circle series approximates
the original amplitude, with its two genuine remainders bounded explicitly. -/
theorem preparedInverseCircleSeries_approximation {T : ℕ} (hT : 1 ≤ T)
    {B : ℝ → ℂ} {A M α φ Λ : ℝ} (hB : IsDerivativeRegular A M (6 * T) B)
    (hBs : ContDiff ℝ ∞ B) (hBP : Periodic B (2 * Real.pi)) (hΛ : 1 ≤ Λ)
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) (u : ℝ)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2)
    (hscale : 800 * (2 * T) * M ^ 2 * Λ⁻¹ ≤ q) :
    ‖preparedInverseCircleSeries T α B φ Λ u - preparedCirclePhaseFactor Λ * B φ‖ ≤
      Real.sqrt (2 * Real.pi / Λ) * (2 * A * (2 * T + 1) * q ^ T) +
        2 * A * Real.sqrt (2 * Real.pi / Λ) *
          circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
            (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / Λ) ^ T := by
  have hΛ₀ : 0 ≤ Λ := by linarith
  have hR₀ := circularStationaryRemainderBase_nonneg T
    (1200 * (T : ℝ) ^ 2 + M)
  have hsum := sum_inverse_stationary_amplitudes_le_two hB.amplitude_nonneg
    (by positivity : 0 ≤ 200 * (T : ℝ) * M ^ 2) (inv_nonneg.mpr hΛ₀)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg (2 * Real.pi / Λ)) hR₀)
      (pow_nonneg (div_nonneg hR₀ hΛ₀) T))
    (inverse_stationary_amplitude_scale_le_half hΛ₀ hq₁ hscale) T
  calc
    _ ≤ Real.sqrt (2 * Real.pi / Λ) * (2 * A * (2 * T + 1) * q ^ T) +
        ∑ j ∈ range T, Λ⁻¹ ^ j * ((A * (200 * T * M ^ 2) ^ j) *
          Real.sqrt (2 * Real.pi / Λ) *
            circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
              (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / Λ) ^ T) :=
      preparedInverseCircleSeries_approximation_sum hT hB hBs hBP hΛ hφ u
        hq₀ hq₁ hscale
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [mul_assoc] using hsum

end FalconerThetaGauge
