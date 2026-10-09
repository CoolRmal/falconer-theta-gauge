/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.StationaryPhaseInverseOperators

/-! # Actual differential action and the inverse-operator cancellation identities -/

@[expose] public section

noncomputable section

open Finset Polynomial
open scoped ContDiff

namespace FalconerThetaGauge

/-- A polynomial acts as its literal finite constant-coefficient differential operator. -/
def polynomialDifferentialAction (p : Polynomial ℂ) (G : ℝ → ℂ) : ℝ → ℂ :=
  fun x => p.sum (fun n c => c * iteratedDeriv n G x)

theorem polynomialDifferentialAction_zero (G : ℝ → ℂ) :
    polynomialDifferentialAction 0 G = 0 := by
  ext x
  simp [polynomialDifferentialAction]

theorem polynomialDifferentialAction_one (G : ℝ → ℂ) :
    polynomialDifferentialAction 1 G = G := by
  ext x
  rw [polynomialDifferentialAction, ← Polynomial.C_1]
  rw [Polynomial.sum_C_index (by simp)]
  simp

theorem polynomialDifferentialAction_monomial (n : ℕ) (c : ℂ) (G : ℝ → ℂ) :
    polynomialDifferentialAction (monomial n c) G = fun x => c * iteratedDeriv n G x := by
  ext x
  simp [polynomialDifferentialAction]

theorem polynomialDifferentialAction_add (p q : Polynomial ℂ) (G : ℝ → ℂ) :
    polynomialDifferentialAction (p + q) G =
      polynomialDifferentialAction p G + polynomialDifferentialAction q G := by
  ext x
  exact Polynomial.sum_add_index p q (fun n c => c * iteratedDeriv n G x)
    (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem polynomialDifferentialAction_sum {ι : Type*} (I : Finset ι)
    (p : ι → Polynomial ℂ) (G : ℝ → ℂ) :
    polynomialDifferentialAction (∑ i ∈ I, p i) G =
      ∑ i ∈ I, polynomialDifferentialAction (p i) G := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [polynomialDifferentialAction_zero]
  | @insert i I hi ih =>
    rw [sum_insert hi, sum_insert hi, polynomialDifferentialAction_add, ih]

theorem polynomialDifferentialAction_neg (p : Polynomial ℂ) (G : ℝ → ℂ) :
    polynomialDifferentialAction (-p) G = -polynomialDifferentialAction p G := by
  have h := polynomialDifferentialAction_add p (-p) G
  rw [add_neg_cancel, polynomialDifferentialAction_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem iteratedDeriv_iteratedDeriv_complex (m n : ℕ) (G : ℝ → ℂ) :
    iteratedDeriv m (iteratedDeriv n G) = iteratedDeriv (m + n) G := by
  simp only [iteratedDeriv_eq_iterate]
  exact (Function.iterate_add_apply deriv m n G).symm

theorem contDiff_iteratedDeriv_complex_infty {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n G) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hG
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem contDiff_polynomialDifferentialAction {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (p : Polynomial ℂ) : ContDiff ℝ ∞ (polynomialDifferentialAction p G) := by
  unfold polynomialDifferentialAction
  simp only [Polynomial.sum_def]
  apply ContDiff.sum
  intro n _
  exact contDiff_const.mul (contDiff_iteratedDeriv_complex_infty hG n)

theorem iteratedDeriv_polynomialDifferentialAction {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (p : Polynomial ℂ) (m : ℕ) (x : ℝ) :
    iteratedDeriv m (polynomialDifferentialAction p G) x =
      ∑ n ∈ p.support, p.coeff n * iteratedDeriv (m + n) G x := by
  unfold polynomialDifferentialAction
  simp only [Polynomial.sum_def]
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_iteratedDeriv_complex]
  · intro n _
    exact (contDiff_const.mul (contDiff_iteratedDeriv_complex_infty hG n)).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) m)

/-- Composition of the actual differential actions agrees with polynomial multiplication. -/
theorem polynomialDifferentialAction_mul {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (p q : Polynomial ℂ) :
    polynomialDifferentialAction (p * q) G =
      polynomialDifferentialAction p (polynomialDifferentialAction q G) := by
  rw [Polynomial.mul_eq_sum_sum, polynomialDifferentialAction_sum]
  simp_rw [Polynomial.sum_def, polynomialDifferentialAction_sum,
    polynomialDifferentialAction_monomial]
  ext x
  simp only [Finset.sum_apply, polynomialDifferentialAction, Polynomial.sum_def]
  simp_rw [iteratedDeriv_polynomialDifferentialAction hG, Finset.mul_sum, mul_assoc]

def stationaryPhaseInverseOperator (j : ℕ) (G : ℝ → ℂ) : ℝ → ℂ :=
  polynomialDifferentialAction (stationaryPhaseInversePolynomial j) G

theorem stationaryPhasePolynomial_action (j : ℕ) (G : ℝ → ℂ) :
    polynomialDifferentialAction (stationaryPhasePolynomial j) G =
      fun x => stationaryPhaseOperator j G x := by
  rw [stationaryPhasePolynomial, polynomialDifferentialAction_sum]
  simp_rw [polynomialDifferentialAction_monomial]
  ext x
  simp only [stationaryPhaseOperator, Finset.sum_apply]

theorem stationaryPhaseInverseOperator_zero (G : ℝ → ℂ) :
    stationaryPhaseInverseOperator 0 G = G := by
  rw [stationaryPhaseInverseOperator, stationaryPhaseInversePolynomial_zero,
    polynomialDifferentialAction_one]

theorem contDiff_stationaryPhaseInverseOperator {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (j : ℕ) : ContDiff ℝ ∞ (stationaryPhaseInverseOperator j G) :=
  contDiff_polynomialDifferentialAction hG _

/-- The polynomial recursion is the literal recursion of the actual differential operators. -/
theorem stationaryPhaseInverseOperator_succ {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    stationaryPhaseInverseOperator (n + 1) G =
      -∑ i ∈ range (n + 1), fun x => stationaryPhaseOperator (i + 1)
        (stationaryPhaseInverseOperator (n - i) G) x := by
  rw [stationaryPhaseInverseOperator, stationaryPhaseInversePolynomial_succ,
    polynomialDifferentialAction_neg, polynomialDifferentialAction_sum]
  simp_rw [polynomialDifferentialAction_mul hG, stationaryPhasePolynomial_action]
  rfl

/-- The actual inverse actions cancel every positive-order coefficient of the stationary series. -/
theorem stationaryPhase_inverse_operator_cancellation {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (j : ℕ) :
    (∑ i ∈ range (j + 1), fun x => stationaryPhaseOperator i
      (stationaryPhaseInverseOperator (j - i) G) x) = if j = 0 then G else 0 := by
  have h := congrArg (fun p => polynomialDifferentialAction p G)
    (stationaryPhasePolynomial_inverse_convolution j)
  rw [polynomialDifferentialAction_sum] at h
  simp_rw [polynomialDifferentialAction_mul hG, stationaryPhasePolynomial_action] at h
  by_cases hj : j = 0
  · simpa [hj, stationaryPhaseInverseOperator, polynomialDifferentialAction_one] using h
  · simpa [hj, stationaryPhaseInverseOperator, polynomialDifferentialAction_zero] using h

/-- The inverse also cancels on the left; all operators have genuinely commuting coefficients. -/
theorem stationaryPhase_operator_inverse_cancellation {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (j : ℕ) :
    (∑ i ∈ range (j + 1), stationaryPhaseInverseOperator (j - i)
      (fun x => stationaryPhaseOperator i G x)) = if j = 0 then G else 0 := by
  have h := congrArg (fun p => polynomialDifferentialAction p G)
    (stationaryPhaseInversePolynomial_convolution j)
  rw [polynomialDifferentialAction_sum] at h
  simp_rw [polynomialDifferentialAction_mul hG, stationaryPhasePolynomial_action] at h
  by_cases hj : j = 0
  · simpa [hj, stationaryPhaseInverseOperator, polynomialDifferentialAction_one] using h
  · simpa [hj, stationaryPhaseInverseOperator, polynomialDifferentialAction_zero] using h

/-- The cancellation remains exact at the source's common stationary-phase scale. -/
theorem stationaryPhase_scaled_inverse_cancellation {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (j : ℕ) (z : ℂ) (x : ℝ) :
    (∑ i ∈ range (j + 1), z ^ i * z ^ (j - i) * stationaryPhaseOperator i
      (stationaryPhaseInverseOperator (j - i) G) x) = if j = 0 then G x else 0 := by
  have h := congrFun (stationaryPhase_inverse_operator_cancellation hG j) x
  have hs : (∑ i ∈ range (j + 1), z ^ i * z ^ (j - i) * stationaryPhaseOperator i
      (stationaryPhaseInverseOperator (j - i) G) x) =
      z ^ j * (∑ i ∈ range (j + 1), stationaryPhaseOperator i
        (stationaryPhaseInverseOperator (j - i) G) x) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hij : i ≤ j := by have := mem_range.mp hi; omega
    rw [← pow_add, Nat.add_sub_of_le hij]
  rw [hs]
  by_cases hj : j = 0
  · simpa [hj, Finset.sum_apply] using h
  · have hzero : (∑ i ∈ range (j + 1), stationaryPhaseOperator i
        (stationaryPhaseInverseOperator (j - i) G) x) = 0 := by
      simpa [hj, Finset.sum_apply] using h
    simp [hzero, hj]

end FalconerThetaGauge
