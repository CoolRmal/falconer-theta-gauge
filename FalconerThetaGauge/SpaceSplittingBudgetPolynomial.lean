module

public import FalconerThetaGauge.SpaceSplittingBudgetScale
public import FalconerThetaGauge.StationaryCircularSource

/-! # Literal polynomial constants in source equation 7.5 are paid by P1 -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_polynomial_le_sourceBudget (T N : ℕ) :
    1280000000 * 16384 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
        ((N : ℝ) ^ 2 + 1) ^ 2 ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12 := by
  have hT : (T : ℝ) ^ 4 ≤ ((T : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 4
  have hTT : ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 ≤ ((T : ℝ) + 1) ^ 12 := by
    calc
      _ ≤ ((T : ℝ) + 1) ^ 4 * ((T : ℝ) + 1) ^ 4 :=
        mul_le_mul_of_nonneg_left hT (by positivity)
      _ = ((T : ℝ) + 1) ^ 8 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
        (by norm_num : 8 ≤ 12)
  have hN : ((N : ℝ) ^ 2 + 1) ^ 2 ≤ ((N : ℝ) + 16) ^ 12 := by
    calc
      _ ≤ (((N : ℝ) + 16) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) N]) 2
      _ = ((N : ℝ) + 16) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
        (by norm_num : 4 ≤ 12)
  have hc : (1280000000 : ℝ) * 16384 ≤ (2 : ℝ) ^ (80 : ℕ) := by norm_num
  calc
    _ = (1280000000 * 16384) * (((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4) *
        ((N : ℝ) ^ 2 + 1) ^ 2 := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul hc hTT (by positivity) (by positivity))
      hN (by positivity) (by positivity)

theorem spaceSplitting_coefficient_polynomial_le_sourceBudget (T N : ℕ) :
    1280 * 16384 * (T : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 1) ^ 2 ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12 := by
  have hT : (T : ℝ) ≤ ((T : ℝ) + 1) ^ 4 := by
    calc
      _ ≤ (T : ℝ) + 1 := by linarith
      _ ≤ _ := le_self_pow₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith) (by decide)
  have hh : 1280 * 16384 * (T : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 1) ^ 2 ≤
      1280000000 * 16384 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
        ((N : ℝ) ^ 2 + 1) ^ 2 := by
    have hc : (1280 : ℝ) ≤ 1280000000 := by norm_num
    have hp := mul_le_mul hc hT (Nat.cast_nonneg _) (by positivity)
    have hpp := mul_le_mul_of_nonneg_right hp
      (by positivity : 0 ≤ 16384 * (T : ℝ) ^ 4 * ((N : ℝ) ^ 2 + 1) ^ 2)
    convert hpp using 1 <;> ring
  exact hh.trans (spaceSplitting_polynomial_le_sourceBudget T N)

theorem spaceSplitting_remainderBase_eq (T : ℕ) (M : ℝ) :
    circularStationaryRemainderBase T (2 * M) = 400000000 * ((T : ℝ) + 1) ^ 4 * M ^ 2 := by
  unfold circularStationaryRemainderBase
  ring

end FalconerThetaGauge
