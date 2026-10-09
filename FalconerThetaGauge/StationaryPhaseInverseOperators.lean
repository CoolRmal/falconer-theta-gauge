/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.StationaryPhaseOperatorsComplex
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Actual recursive inverse polynomials of the stationary-phase operators -/

@[expose] public section

noncomputable section

open Finset Polynomial

namespace FalconerThetaGauge

/-- The polynomial of the actual constant coefficients proved in Lemma 3.6. -/
def stationaryPhasePolynomial (j : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (2 * j + 1), monomial k (stationaryPhaseCoefficient j k)

theorem stationaryPhasePolynomial_zero : stationaryPhasePolynomial 0 = 1 := by
  simp [stationaryPhasePolynomial, stationaryPhaseCoefficient_zero]

theorem stationaryPhasePolynomial_natDegree_le (j : ℕ) :
    (stationaryPhasePolynomial j).natDegree ≤ 2 * j := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_monomial_le _).trans (by have := mem_range.mp hk; omega)

theorem stationaryPhasePolynomial_coeff (j k : ℕ) :
    (stationaryPhasePolynomial j).coeff k = stationaryPhaseCoefficient j k := by
  classical
  unfold stationaryPhasePolynomial
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases hk : k < 2 * j + 1
  · simp [mem_range.mpr hk]
  · have hzero := stationaryPhaseCoefficient_eq_zero (by omega : 2 * j < k)
    simp [hk, hzero]

/-- The literal source recursion `Q_j = -∑_{i=1}^j P_i Q_{j-i}`. -/
def stationaryPhaseInversePolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => -∑ i ∈ range (n + 1),
      stationaryPhasePolynomial (i + 1) * stationaryPhaseInversePolynomial (n - i)
termination_by j => j
decreasing_by omega

theorem stationaryPhaseInversePolynomial_zero : stationaryPhaseInversePolynomial 0 = 1 := by
  rw [stationaryPhaseInversePolynomial]

theorem stationaryPhaseInversePolynomial_succ (n : ℕ) :
    stationaryPhaseInversePolynomial (n + 1) = -∑ i ∈ range (n + 1),
      stationaryPhasePolynomial (i + 1) * stationaryPhaseInversePolynomial (n - i) := by
  rw [stationaryPhaseInversePolynomial]

/-- Every recursively constructed inverse operator has differential order at most `2j`. -/
theorem stationaryPhaseInversePolynomial_natDegree_le (j : ℕ) :
    (stationaryPhaseInversePolynomial j).natDegree ≤ 2 * j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [stationaryPhaseInversePolynomial_zero]
    | succ n =>
      rw [stationaryPhaseInversePolynomial_succ, natDegree_neg]
      apply natDegree_sum_le_of_forall_le
      intro i hi
      have hiN : i ≤ n := by have := mem_range.mp hi; omega
      have hdeg := natDegree_mul_le_of_le (stationaryPhasePolynomial_natDegree_le (i + 1))
        (ih (n - i) (by omega))
      exact hdeg.trans (by omega)

theorem stationaryPhaseInversePolynomial_coeff_eq_zero {j k : ℕ} (hk : 2 * j < k) :
    (stationaryPhaseInversePolynomial j).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((stationaryPhaseInversePolynomial_natDegree_le j).trans_lt hk)

/-- Exact convolution cancellation, derived from the recursion. -/
theorem stationaryPhasePolynomial_inverse_convolution (j : ℕ) :
    (∑ i ∈ range (j + 1),
      stationaryPhasePolynomial i * stationaryPhaseInversePolynomial (j - i)) =
        if j = 0 then 1 else 0 := by
  cases j with
  | zero => simp [stationaryPhasePolynomial_zero, stationaryPhaseInversePolynomial_zero]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [stationaryPhasePolynomial_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    rw [stationaryPhaseInversePolynomial_succ]
    exact add_neg_cancel _

/-- Commutativity gives cancellation with the inverse operators on the other side. -/
theorem stationaryPhaseInversePolynomial_convolution (j : ℕ) :
    (∑ i ∈ range (j + 1),
      stationaryPhaseInversePolynomial (j - i) * stationaryPhasePolynomial i) =
        if j = 0 then 1 else 0 := by
  simpa only [mul_comm] using stationaryPhasePolynomial_inverse_convolution j

end FalconerThetaGauge
