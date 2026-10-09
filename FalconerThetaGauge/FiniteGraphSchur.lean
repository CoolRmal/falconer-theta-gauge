module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Schur's bound for the actual finite symmetric linking graph -/

@[expose] public section

noncomputable section

open Finset
open scoped InnerProductSpace

namespace FalconerThetaGauge

theorem finite_graph_schur {ι : Type*} (s : Finset ι) (linked : ι → ι → Prop)
    [DecidableRel linked] (hsym : ∀ ⦃i j⦄, linked i j → linked j i) (a : ι → ℝ) {D : ℝ}
    (hdegree : ∀ i ∈ s, ((s.filter (linked i)).card : ℝ) ≤ D) :
    (∑ i ∈ s, ∑ j ∈ s, if linked i j then a i * a j else 0) ≤
      D * ∑ i ∈ s, a i ^ 2 := by
  have hrow : (∑ i ∈ s, ∑ j ∈ s, if linked i j then a i ^ 2 else 0) ≤
      D * ∑ i ∈ s, a i ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hdegree i hi) (sq_nonneg _)
  have hcol : (∑ i ∈ s, ∑ j ∈ s, if linked i j then a j ^ 2 else 0) ≤
      D * ∑ i ∈ s, a i ^ 2 := by
    calc
      _ = ∑ j ∈ s, ∑ i ∈ s, if linked j i then a j ^ 2 else 0 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro j hj
        apply sum_congr rfl
        intro i hi
        have he : linked i j ↔ linked j i := ⟨fun h ↦ hsym h, fun h ↦ hsym h⟩
        simp only [he]
      _ ≤ _ := hrow
  have hpair : 2 * (∑ i ∈ s, ∑ j ∈ s,
      if linked i j then a i * a j else 0) ≤
      (∑ i ∈ s, ∑ j ∈ s, if linked i j then a i ^ 2 else 0) +
      (∑ i ∈ s, ∑ j ∈ s, if linked i j then a j ^ 2 else 0) := by
    simp_rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    split_ifs <;> nlinarith [sq_nonneg (a i - a j)]
  linarith

/-- The genuine squared norm of a finite sum, with all unlinked inner products retained. -/
theorem norm_sum_sq_le_graph_schur {ι F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (s : Finset ι) (linked : ι → ι → Prop)
    [DecidableRel linked] (hsym : ∀ ⦃i j⦄, linked i j → linked j i) (z : ι → F) {D : ℝ}
    (hdegree : ∀ i ∈ s, ((s.filter (linked i)).card : ℝ) ≤ D) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ D * (∑ i ∈ s, ‖z i‖ ^ 2) +
      ∑ i ∈ s, ∑ j ∈ s, if linked i j then 0 else |⟪z i, z j⟫_ℝ| := by
  have hsum : ‖∑ i ∈ s, z i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, ⟪z i, z j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ((if linked i j then ‖z i‖ * ‖z j‖ else 0) +
        (if linked i j then 0 else |⟪z i, z j⟫_ℝ|)) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      split_ifs with h
      · simpa only [add_zero] using real_inner_le_norm (z i) (z j)
      · simpa only [zero_add] using le_abs_self (⟪z i, z j⟫_ℝ)
    _ = (∑ i ∈ s, ∑ j ∈ s, if linked i j then ‖z i‖ * ‖z j‖ else 0) +
        ∑ i ∈ s, ∑ j ∈ s, if linked i j then 0 else |⟪z i, z j⟫_ℝ| := by
      simp only [sum_add_distrib]
    _ ≤ _ := add_le_add_left (finite_graph_schur s linked hsym (fun i ↦ ‖z i‖) hdegree) _

end FalconerThetaGauge
