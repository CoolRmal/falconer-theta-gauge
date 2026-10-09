module

public import FalconerThetaGauge.SpaceSplittingCoefficients
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # The two stationary-order sums with literal geometric coefficient decay -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

theorem nat_successor_sq_le_three_two_pow (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 ≤ 3 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases n with _ | n
    · norm_num
    rcases n with _ | n
    · norm_num
    have hn : (2 : ℝ) ≤ (n + 1 + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ n + 1 + 1)
    push_cast at *
    rw [pow_succ (2 : ℝ) (n + 1 + 1)]
    nlinarith

theorem sum_geometric_quarter_le_two (T : ℕ) :
    ∑ j ∈ range T, (1 / (4 : ℝ)) ^ j ≤ 2 := by
  apply le_trans _ (sum_geometric_two_le T)
  apply sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) j

theorem sum_successor_sq_geometric_quarter_le_six (T : ℕ) :
    ∑ j ∈ range T, ((j : ℝ) + 1) ^ 2 * (1 / (4 : ℝ)) ^ j ≤ 6 := by
  calc
    _ ≤ ∑ j ∈ range T, (3 * 2 ^ j) * (1 / (4 : ℝ)) ^ j := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (nat_successor_sq_le_three_two_pow j)
        (by positivity)
    _ = 3 * ∑ j ∈ range T, (1 / (2 : ℝ)) ^ j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ 6 := by linarith [sum_geometric_two_le T]

/-- Both opposite stationary signs cost at most the source's numerical `100`. -/
theorem stationary_order_double_geometric_sum_le_fifty (T : ℕ) :
    ∑ j ∈ range T, ∑ k ∈ range T,
      ((j : ℝ) + k + 2) ^ 2 * (1 / (4 : ℝ)) ^ (j + k) ≤ 50 := by
  have hq := sum_geometric_quarter_le_two T
  have hp := sum_successor_sq_geometric_quarter_le_six T
  have hqn : 0 ≤ ∑ j ∈ range T, (1 / (4 : ℝ)) ^ j := sum_nonneg (by intros; positivity)
  have hpn : 0 ≤ ∑ j ∈ range T, ((j : ℝ) + 1) ^ 2 * (1 / (4 : ℝ)) ^ j :=
    sum_nonneg (by intros; positivity)
  calc
    _ ≤ ∑ j ∈ range T, ∑ k ∈ range T,
        (2 * ((j : ℝ) + 1) ^ 2 + 2 * ((k : ℝ) + 1) ^ 2) *
          (1 / (4 : ℝ)) ^ (j + k) := by
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg ((j : ℝ) - k)]
    _ = 4 * (∑ j ∈ range T, ((j : ℝ) + 1) ^ 2 * (1 / (4 : ℝ)) ^ j) *
        (∑ j ∈ range T, (1 / (4 : ℝ)) ^ j) := by
      have hterm (j k : ℕ) :
          (2 * ((j : ℝ) + 1) ^ 2 + 2 * ((k : ℝ) + 1) ^ 2) *
            (1 / (4 : ℝ)) ^ (j + k) =
          (2 * (((j : ℝ) + 1) ^ 2 * (1 / (4 : ℝ)) ^ j)) * (1 / (4 : ℝ)) ^ k +
            (2 * (1 / (4 : ℝ)) ^ j) * (((k : ℝ) + 1) ^ 2 * (1 / (4 : ℝ)) ^ k) := by
        rw [pow_add]
        ring
      simp_rw [hterm, sum_add_distrib, ← mul_sum, ← sum_mul]
      rw [← mul_sum, ← mul_sum]
      ring
    _ ≤ 50 := by nlinarith [mul_le_mul hp hq hqn (by norm_num : (0 : ℝ) ≤ 6)]

theorem two_stationary_order_double_geometric_sum_le_hundred (T : ℕ) :
    2 * (∑ j ∈ range T, ∑ k ∈ range T,
      ((j : ℝ) + k + 2) ^ 2 * (1 / (4 : ℝ)) ^ (j + k)) ≤ 100 := by
  linarith [stationary_order_double_geometric_sum_le_fifty T]

end FalconerThetaGauge
