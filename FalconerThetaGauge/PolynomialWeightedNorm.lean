module

public import FalconerThetaGauge.StationaryPhaseInverseOperators
public import FalconerThetaGauge.StationaryPhaseOperatorBudget

/-! # Weighted coefficient norms of actual complex polynomials -/

@[expose] public section

noncomputable section

open Finset Polynomial

namespace FalconerThetaGauge

def polynomialWeightedNorm (p : Polynomial ℂ) (M : ℝ) : ℝ :=
  p.sum fun k a ↦ ‖a‖ * M ^ k

theorem polynomialWeightedNorm_nonneg (p : Polynomial ℂ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ polynomialWeightedNorm p M :=
  sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hM _)

theorem polynomialWeightedNorm_eq_sum_range (p : Polynomial ℂ) (M : ℝ) {n : ℕ}
    (hn : p.natDegree ≤ n) :
    polynomialWeightedNorm p M = ∑ k ∈ range (n + 1), ‖p.coeff k‖ * M ^ k := by
  apply Polynomial.sum_eq_of_subset
  · intro k; simp
  · intro k hk
    exact mem_range.mpr (by
      have := (le_natDegree_of_ne_zero (mem_support_iff.mp hk)).trans hn
      omega)

theorem polynomialWeightedNorm_add_le (p q : Polynomial ℂ) {M : ℝ} (hM : 0 ≤ M) :
    polynomialWeightedNorm (p + q) M ≤ polynomialWeightedNorm p M +
      polynomialWeightedNorm q M := by
  classical
  let s := p.support ∪ q.support
  have hzero : ∀ k : ℕ, ‖(0 : ℂ)‖ * M ^ k = 0 := by simp
  rw [polynomialWeightedNorm, Polynomial.sum_eq_of_subset _ hzero support_add]
  rw [polynomialWeightedNorm, Polynomial.sum_eq_of_subset _ hzero subset_union_left]
  rw [polynomialWeightedNorm, Polynomial.sum_eq_of_subset _ hzero subset_union_right]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  simpa only [coeff_add, add_mul] using
    mul_le_mul_of_nonneg_right (norm_add_le (p.coeff k) (q.coeff k)) (pow_nonneg hM k)

theorem polynomialWeightedNorm_sum_le {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ℂ) {M : ℝ} (hM : 0 ≤ M) :
    polynomialWeightedNorm (∑ i ∈ s, p i) M ≤ ∑ i ∈ s, polynomialWeightedNorm (p i) M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialWeightedNorm]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (polynomialWeightedNorm_add_le _ _ hM).trans (add_le_add_right ih _)

theorem polynomialWeightedNorm_neg (p : Polynomial ℂ) (M : ℝ) :
    polynomialWeightedNorm (-p) M = polynomialWeightedNorm p M := by
  rw [polynomialWeightedNorm_eq_sum_range _ M (by rw [natDegree_neg]),
    polynomialWeightedNorm_eq_sum_range p M (le_refl _)]
  simp

theorem polynomialWeightedNorm_monomial (k : ℕ) (a : ℂ) (M : ℝ) :
    polynomialWeightedNorm (monomial k a) M = ‖a‖ * M ^ k := by
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem polynomialWeightedNorm_one (M : ℝ) :
    polynomialWeightedNorm 1 M = 1 := by
  rw [← monomial_zero_one, polynomialWeightedNorm_monomial]
  simp

theorem polynomialWeightedNorm_mul_le (p q : Polynomial ℂ) {M : ℝ} (hM : 0 ≤ M) :
    polynomialWeightedNorm (p * q) M ≤ polynomialWeightedNorm p M *
      polynomialWeightedNorm q M := by
  classical
  rw [Polynomial.mul_eq_sum_sum]
  calc
    _ ≤ ∑ i ∈ p.support, polynomialWeightedNorm
        (q.sum fun j a ↦ monomial (i + j) (p.coeff i * a)) M :=
      polynomialWeightedNorm_sum_le _ _ hM
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        polynomialWeightedNorm (monomial (i + j) (p.coeff i * q.coeff j)) M := by
      exact sum_le_sum fun i _ ↦ polynomialWeightedNorm_sum_le _ _ hM
    _ = _ := by
      simp_rw [polynomialWeightedNorm_monomial, norm_mul, pow_add]
      change _ = (∑ i ∈ p.support, ‖p.coeff i‖ * M ^ i) *
        (∑ j ∈ q.support, ‖q.coeff j‖ * M ^ j)
      rw [sum_mul]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring

end FalconerThetaGauge
