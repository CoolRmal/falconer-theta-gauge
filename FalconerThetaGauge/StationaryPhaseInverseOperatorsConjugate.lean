/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.StationaryPhaseInverseOperatorsAction

/-! # The actual inverse at the opposite stationary point -/

@[expose] public section

noncomputable section

open Finset Polynomial
open scoped ContDiff

namespace FalconerThetaGauge

def stationaryPhaseConjugatePolynomial (j : ℕ) : Polynomial ℂ :=
  (stationaryPhasePolynomial j).map (starRingEnd ℂ)

def stationaryPhaseConjugateInversePolynomial (j : ℕ) : Polynomial ℂ :=
  (stationaryPhaseInversePolynomial j).map (starRingEnd ℂ)

theorem stationaryPhaseConjugatePolynomial_coeff (j k : ℕ) :
    (stationaryPhaseConjugatePolynomial j).coeff k = stationaryPhaseConjugateCoefficient j k := by
  simp [stationaryPhaseConjugatePolynomial, Polynomial.coeff_map,
    stationaryPhasePolynomial_coeff, stationaryPhaseConjugateCoefficient]

theorem stationaryPhaseConjugateInversePolynomial_zero :
    stationaryPhaseConjugateInversePolynomial 0 = 1 := by
  simp [stationaryPhaseConjugateInversePolynomial, stationaryPhaseInversePolynomial_zero]

theorem stationaryPhaseConjugateInversePolynomial_succ (n : ℕ) :
    stationaryPhaseConjugateInversePolynomial (n + 1) = -∑ i ∈ range (n + 1),
      stationaryPhaseConjugatePolynomial (i + 1) *
        stationaryPhaseConjugateInversePolynomial (n - i) := by
  simp [stationaryPhaseConjugateInversePolynomial, stationaryPhaseInversePolynomial_succ,
    stationaryPhaseConjugatePolynomial, Polynomial.map_sum, Polynomial.map_mul]

theorem stationaryPhaseConjugateInversePolynomial_natDegree_le (j : ℕ) :
    (stationaryPhaseConjugateInversePolynomial j).natDegree ≤ 2 * j :=
  Polynomial.natDegree_map_le.trans (stationaryPhaseInversePolynomial_natDegree_le j)

theorem norm_stationaryPhaseConjugateInversePolynomial_coeff (j k : ℕ) :
    ‖(stationaryPhaseConjugateInversePolynomial j).coeff k‖ =
      ‖(stationaryPhaseInversePolynomial j).coeff k‖ := by
  simp [stationaryPhaseConjugateInversePolynomial, Polynomial.coeff_map]

theorem stationaryPhaseConjugatePolynomial_inverse_convolution (j : ℕ) :
    (∑ i ∈ range (j + 1), stationaryPhaseConjugatePolynomial i *
      stationaryPhaseConjugateInversePolynomial (j - i)) = if j = 0 then 1 else 0 := by
  have h := congrArg (fun p : Polynomial ℂ => p.map (starRingEnd ℂ))
    (stationaryPhasePolynomial_inverse_convolution j)
  by_cases hj : j = 0
  · simpa [hj, stationaryPhaseConjugatePolynomial, stationaryPhaseConjugateInversePolynomial,
      Polynomial.map_sum, Polynomial.map_mul] using h
  · simpa [hj, stationaryPhaseConjugatePolynomial, stationaryPhaseConjugateInversePolynomial,
      Polynomial.map_sum, Polynomial.map_mul] using h

def stationaryPhaseConjugateInverseOperator (j : ℕ) (G : ℝ → ℂ) : ℝ → ℂ :=
  polynomialDifferentialAction (stationaryPhaseConjugateInversePolynomial j) G

theorem stationaryPhaseConjugatePolynomial_action (j : ℕ) (G : ℝ → ℂ) :
    polynomialDifferentialAction (stationaryPhaseConjugatePolynomial j) G =
      fun x => stationaryPhaseConjugateOperator j G x := by
  unfold stationaryPhaseConjugatePolynomial stationaryPhasePolynomial
  rw [Polynomial.map_sum, polynomialDifferentialAction_sum]
  simp_rw [Polynomial.map_monomial, polynomialDifferentialAction_monomial]
  ext x
  simp only [stationaryPhaseConjugateOperator, stationaryPhaseConjugateCoefficient,
    Finset.sum_apply, starRingEnd_apply]

theorem stationaryPhase_conjugate_inverse_operator_cancellation
    {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (j : ℕ) :
    (∑ i ∈ range (j + 1), fun x => stationaryPhaseConjugateOperator i
      (stationaryPhaseConjugateInverseOperator (j - i) G) x) = if j = 0 then G else 0 := by
  have h := congrArg (fun p => polynomialDifferentialAction p G)
    (stationaryPhaseConjugatePolynomial_inverse_convolution j)
  rw [polynomialDifferentialAction_sum] at h
  simp_rw [polynomialDifferentialAction_mul hG, stationaryPhaseConjugatePolynomial_action] at h
  by_cases hj : j = 0
  · simpa [hj, stationaryPhaseConjugateInverseOperator, polynomialDifferentialAction_one] using h
  · simpa [hj, stationaryPhaseConjugateInverseOperator, polynomialDifferentialAction_zero] using h

end FalconerThetaGauge
