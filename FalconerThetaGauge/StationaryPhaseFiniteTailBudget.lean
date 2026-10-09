module

public import FalconerThetaGauge.StationaryPhaseFiniteInversion

/-! # A summable numerical bound for the genuine finite inversion tail -/

@[expose] public section

noncomputable section

open Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem sum_geometric_le_two {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) (n : ℕ) :
    (∑ k ∈ range n, q ^ k) ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ']
    simp only [pow_zero, pow_succ']
    rw [← mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left ih hq₀]

theorem finite_stationary_tail_numeric_le {A q : ℝ} (hA : 0 ≤ A)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) (T : ℕ) :
    (∑ k ∈ range T, A * (T + k + 1) * q ^ (T + k)) ≤
      2 * A * (2 * T + 1) * q ^ T := by
  calc
    _ ≤ ∑ k ∈ range T, A * (2 * T + 1) * (q ^ T * q ^ k) := by
      apply sum_le_sum
      intro k hk
      rw [pow_add]
      have hkT : k < T := mem_range.mp hk
      have hkR : (k : ℝ) ≤ T := by exact_mod_cast (le_of_lt hkT)
      gcongr
      linarith
    _ = A * (2 * T + 1) * q ^ T * ∑ k ∈ range T, q ^ k := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ A * (2 * T + 1) * q ^ T * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_le_two hq₀ hq₁ T) (by positivity)
    _ = _ := by ring

/-- The actual omitted operators satisfy a geometric tail estimate at the actual scale. -/
theorem norm_stationaryPhaseFiniteTail_le_geometric {G : ℝ → ℂ} (hGs : ContDiff ℝ ∞ G)
    {T : ℕ} (hT : 0 < T) {A M : ℝ} (hG : IsDerivativeRegular A M (4 * T) G)
    (z : ℂ) (φ : ℝ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2)
    (hscale : 800 * (2 * T) * M ^ 2 * ‖z‖ ≤ q) :
    ‖stationaryPhaseFiniteTail T z G φ‖ ≤ 2 * A * (2 * T + 1) * q ^ T := by
  calc
    _ ≤ ∑ k ∈ range T, A * (T + k + 1) *
        (800 * (T + k) * M ^ 2 * ‖z‖) ^ (T + k) :=
      norm_stationaryPhaseFiniteTail_le hGs hT hG z φ
    _ ≤ ∑ k ∈ range T, A * (T + k + 1) * q ^ (T + k) := by
      apply sum_le_sum
      intro k hk
      have hkT : k < T := mem_range.mp hk
      apply mul_le_mul_of_nonneg_left _ (by positivity [hG.amplitude_nonneg])
      apply pow_le_pow_left₀ (by positivity)
      apply le_trans _ hscale
      have hkR : (T + k : ℝ) ≤ 2 * T := by exact_mod_cast (by omega : T + k ≤ 2 * T)
      gcongr
    _ ≤ _ := finite_stationary_tail_numeric_le hG.amplitude_nonneg hq₀ hq₁ T

end FalconerThetaGauge
