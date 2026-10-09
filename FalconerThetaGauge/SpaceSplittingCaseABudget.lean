module

public import FalconerThetaGauge.SpaceSplittingBudgetRemainder
public import FalconerThetaGauge.SpaceSplittingCaseALinear
public import FalconerThetaGauge.SpaceSplittingCoefficients

/-! # The literal linear radial ratio has uniform source decay -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_linear_polynomial_le_sourceBudget (T N : ℕ) :
    960 * (T : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12 := by
  have ht : (T : ℝ) ^ 2 ≤ ((T : ℝ) + 1) ^ 12 := by
    calc
      _ ≤ ((T : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
        (by norm_num : 2 ≤ 12)
  have hn : 1 ≤ ((N : ℝ) + 16) ^ 12 :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  calc
    _ ≤ (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 := mul_le_mul
      (by norm_num : (960 : ℝ) ≤ 2 ^ (80 : ℕ)) ht (by positivity) (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hn

theorem spaceSplitting_linear_ratio_le {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) {h v d : ℝ}
    (hgap : 2 * (tolerance θ N * N) ≤ v - h)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    1200 * (expansionCount θ N : ℝ) ^ 2 / ((2 : ℝ) ^ v * d) ≤
      (2 : ℝ) ^ (-15 * (tolerance θ N * N) / 8) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  have hi := spaceSplitting_inv_dyadic_distance_le (v := v) hd
  rw [div_eq_mul_inv]
  calc
    _ ≤ 1200 * (T : ℝ) ^ 2 * ((4 / 5 : ℝ) * (2 : ℝ) ^ (h - v)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 960 * (T : ℝ) ^ 2 * (2 : ℝ) ^ (h - v) := by ring
    _ ≤ 960 * (T : ℝ) ^ 2 * (2 : ℝ) ^ (-2 * E) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) (by positivity)
    _ ≤ ((2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12) *
        (2 : ℝ) ^ (-2 * E) := mul_le_mul_of_nonneg_right
      (spaceSplitting_linear_polynomial_le_sourceBudget T N) (by positivity)
    _ ≤ (2 : ℝ) ^ (E / 8) * (2 : ℝ) ^ (-2 * E) :=
      mul_le_mul_of_nonneg_right hpar.2.1 (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [E]
      ring

theorem spaceSplitting_linear_ratio_pow_le {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) {h v d : ℝ}
    (hgap : 2 * (tolerance θ N * N) ≤ v - h)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    (1200 * (expansionCount θ N : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ expansionCount θ N ≤
      (2 : ℝ) ^ (-450 * (N : ℝ)) := by
  have hd₀ : 0 < d := lt_of_lt_of_le (by positivity) hd
  exact (pow_le_pow_left₀ (by positivity)
    (spaceSplitting_linear_ratio_le hpar hgap hd) _).trans
      (spaceSplitting_decay_ratio_pow_le hpar)

end FalconerThetaGauge
