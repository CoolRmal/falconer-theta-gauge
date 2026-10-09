module

public import FalconerThetaGauge.PolynomialWeightedNorm

/-! # Numerical norms of the actual recursively constructed inverse operators -/

@[expose] public section

noncomputable section

open Finset Polynomial

namespace FalconerThetaGauge

theorem stationaryPhasePolynomial_weightedNorm (j : ℕ) (M : ℝ) :
    polynomialWeightedNorm (stationaryPhasePolynomial j) M = stationaryPhaseWeightedNorm j M := by
  rw [polynomialWeightedNorm_eq_sum_range _ M (stationaryPhasePolynomial_natDegree_le j)]
  simp only [stationaryPhaseWeightedNorm, stationaryPhasePolynomial_coeff]

theorem inverse_budget_convolution (a : ℝ) (n : ℕ) :
    (∑ i ∈ range (n + 1), a ^ (i + 1) * (2 * a) ^ (n - i)) =
      (2 * a) ^ (n + 1) - a ^ (n + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ]
    have hsum : (∑ i ∈ range (n + 1), a ^ (i + 1) * (2 * a) ^ (n + 1 - i)) =
        (2 * a) * ∑ i ∈ range (n + 1), a ^ (i + 1) * (2 * a) ^ (n - i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hin : i ≤ n := by have := mem_range.mp hi; omega
      rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
      ring
    rw [hsum, ih]
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [pow_succ, pow_succ]
    ring

theorem stationaryPhaseInversePolynomial_weightedNorm_uniform {M : ℝ} (hM : 1 ≤ M)
    (N : ℕ) {j : ℕ} (hj : j ≤ N) :
    polynomialWeightedNorm (stationaryPhaseInversePolynomial j) M ≤
      (200 * N * M ^ 2) ^ j := by
  have hM0 : 0 ≤ M := by linarith
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [stationaryPhaseInversePolynomial_zero, polynomialWeightedNorm_one]
    | succ n =>
      rw [stationaryPhaseInversePolynomial_succ, polynomialWeightedNorm_neg]
      calc
        _ ≤ ∑ i ∈ range (n + 1), polynomialWeightedNorm
            (stationaryPhasePolynomial (i + 1) * stationaryPhaseInversePolynomial (n - i)) M :=
          polynomialWeightedNorm_sum_le _ _ hM0
        _ ≤ ∑ i ∈ range (n + 1),
            (100 * N * M ^ 2) ^ (i + 1) * (200 * N * M ^ 2) ^ (n - i) := by
          apply sum_le_sum
          intro i hi
          have hin : i ≤ n := by have := mem_range.mp hi; omega
          have hiN : i + 1 ≤ N := by omega
          apply (polynomialWeightedNorm_mul_le _ _ hM0).trans
          apply mul_le_mul
          · rw [stationaryPhasePolynomial_weightedNorm]
            have hiR : (i + 1 : ℝ) ≤ N := by exact_mod_cast hiN
            exact (stationaryPhaseWeightedNorm_le (by omega : 1 ≤ i + 1) hM).trans
              (pow_le_pow_left₀ (by positivity) (by
                simp only [Nat.cast_add, Nat.cast_one]
                gcongr) _)
          · exact ih (n - i) (by omega) (by omega)
          · exact polynomialWeightedNorm_nonneg _ hM0
          · positivity
        _ = (200 * N * M ^ 2) ^ (n + 1) - (100 * N * M ^ 2) ^ (n + 1) := by
          have he : (200 * N * M ^ 2 : ℝ) = 2 * (100 * N * M ^ 2) := by ring
          rw [he, inverse_budget_convolution]
        _ ≤ _ := sub_le_self _ (by positivity)

/-- The manuscript's inverse-operator bound follows from the stronger actual `200` budget. -/
theorem stationaryPhaseInversePolynomial_weightedNorm_le {j : ℕ} {M : ℝ} (hM : 1 ≤ M) :
    polynomialWeightedNorm (stationaryPhaseInversePolynomial j) M ≤
      (800 * j * M ^ 2) ^ j := by
  exact (stationaryPhaseInversePolynomial_weightedNorm_uniform hM j (le_refl j)).trans
    (pow_le_pow_left₀ (by positivity) (by gcongr; norm_num) _)

end FalconerThetaGauge
