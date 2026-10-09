/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.StationaryPhaseInverseOperatorsAction
public import FalconerThetaGauge.RegularFunctions

/-! # Finite-order smoothness of the literal polynomial differential action -/

@[expose] public section

noncomputable section

open Finset Polynomial
open scoped ContDiff

namespace FalconerThetaGauge

theorem contDiff_iteratedDeriv_complex_finite {G : ℝ → ℂ} {K d n : ℕ}
    (hG : ContDiff ℝ (K + d : ℕ) G) (hn : n ≤ d) :
    ContDiff ℝ K (iteratedDeriv n G) := by
  have hh := contDiff_nat_iff_iteratedDeriv.mp hG
  rw [contDiff_nat_iff_iteratedDeriv]
  constructor
  · intro m hm
    rw [iteratedDeriv_iteratedDeriv_complex]
    exact hh.1 (m + n) (by omega)
  · intro m hm
    rw [iteratedDeriv_iteratedDeriv_complex]
    exact hh.2 (m + n) (by omega)

theorem contDiff_polynomialDifferentialAction_of_natDegree_le {G : ℝ → ℂ} {K d : ℕ}
    (hG : ContDiff ℝ (K + d : ℕ) G) (p : Polynomial ℂ) (hp : p.natDegree ≤ d) :
    ContDiff ℝ K (polynomialDifferentialAction p G) := by
  unfold polynomialDifferentialAction
  simp only [Polynomial.sum_def]
  apply ContDiff.sum
  intro n hn
  exact contDiff_const.mul
    (contDiff_iteratedDeriv_complex_finite hG ((le_natDegree_of_mem_supp n hn).trans hp))

/-- The exact derivative formula needs only the indicated finite differentiability. -/
theorem iteratedDeriv_polynomialDifferentialAction_of_natDegree_le
    {G : ℝ → ℂ} {K d : ℕ} (hG : ContDiff ℝ (K + d : ℕ) G)
    (p : Polynomial ℂ) (hp : p.natDegree ≤ d) {m : ℕ} (hm : m ≤ K) (x : ℝ) :
    iteratedDeriv m (polynomialDifferentialAction p G) x =
      ∑ n ∈ p.support, p.coeff n * iteratedDeriv (m + n) G x := by
  unfold polynomialDifferentialAction
  simp only [Polynomial.sum_def]
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_iteratedDeriv_complex]
  · intro n hn
    exact (contDiff_const.mul
      (contDiff_iteratedDeriv_complex_finite hG
        ((le_natDegree_of_mem_supp n hn).trans hp))).contDiffAt.of_le
          (by exact_mod_cast hm)

end FalconerThetaGauge
