module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Quantitative finite partition weights for Gevrey composition

The bounds count the literal ordered partitions in Faà di Bruno's formula.
-/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

def stationaryPartitionWeight {n : ℕ} (c : OrderedFinpartition n) : ℕ :=
  c.length.factorial ^ 2 * ∏ i, (c.partSize i).factorial

theorem orderedFinpartition_sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr c.equivSigma

theorem stationaryPartitionWeight_extendLeft {n : ℕ} (c : OrderedFinpartition n) :
    stationaryPartitionWeight c.extendLeft = (c.length + 1) ^ 2 *
      stationaryPartitionWeight c := by
  change (c.length + 1).factorial ^ 2 *
    (∏ x : Fin (c.length + 1), Nat.factorial ((Fin.cons (α := fun _ ↦ ℕ) 1 c.partSize) x)) =
      (c.length + 1) ^ 2 * (c.length.factorial ^ 2 * ∏ i, (c.partSize i).factorial)
  simp only [Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Nat.factorial_succ, Nat.factorial_zero, mul_one]
  ring

theorem stationaryPartitionWeight_extendMiddle {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) :
    stationaryPartitionWeight (c.extendMiddle i) = (c.partSize i + 1) *
      stationaryPartitionWeight c := by
  classical
  have hfun : (fun j ↦ ((Function.update c.partSize i (c.partSize i + 1)) j).factorial) =
      Function.update (fun j ↦ (c.partSize j).factorial) i (c.partSize i + 1).factorial := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  change c.length.factorial ^ 2 *
    (∏ x : Fin c.length, ((Function.update c.partSize i (c.partSize i + 1)) x).factorial) =
      (c.partSize i + 1) * (c.length.factorial ^ 2 * ∏ i, (c.partSize i).factorial)
  rw [hfun]
  rw [prod_update_of_mem (mem_univ i), Nat.factorial_succ,
    ← mul_assoc, ← mul_assoc]
  rw [sdiff_singleton_eq_erase]
  rw [← mul_prod_erase _ _ (mem_univ i)]
  ring

theorem stationaryPartitionWeight_sum_extend {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Option (Fin c.length), stationaryPartitionWeight (c.extend i) =
      ((c.length + 1) ^ 2 + n + c.length) * stationaryPartitionWeight c := by
  classical
  rw [Fintype.sum_option]
  simp only [OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    stationaryPartitionWeight_extendLeft, stationaryPartitionWeight_extendMiddle]
  rw [← sum_mul, sum_add_distrib, orderedFinpartition_sum_partSize]
  simp only [sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one]
  ring

/-- An actual weighted sum over all partitions, with only a fixed exponential loss. -/
theorem sum_stationaryPartitionWeight_le (n : ℕ) :
    ∑ c : OrderedFinpartition n, stationaryPartitionWeight c ≤ 3 ^ n * n.factorial ^ 2 := by
  classical
  induction n with
  | zero => simp [stationaryPartitionWeight, OrderedFinpartition.default_eq,
      OrderedFinpartition.atomic]
  | succ n ih =>
    have he : (∑ c : OrderedFinpartition (n + 1), stationaryPartitionWeight c) =
        ∑ c : OrderedFinpartition n, ∑ i : Option (Fin c.length),
          stationaryPartitionWeight (c.extend i) := by
      have h := (Fintype.sum_equiv (OrderedFinpartition.extendEquiv n)
        (fun p ↦ stationaryPartitionWeight (p.1.extend p.2))
        stationaryPartitionWeight (fun _ ↦ rfl)).symm
      simpa only [Fintype.sum_sigma] using h
    rw [he]
    simp_rw [stationaryPartitionWeight_sum_extend]
    calc
      _ ≤ ∑ c : OrderedFinpartition n, (3 * (n + 1) ^ 2) * stationaryPartitionWeight c := by
        apply sum_le_sum
        intro c _
        apply Nat.mul_le_mul_right
        have hc := c.length_le
        nlinarith
      _ = (3 * (n + 1) ^ 2) * ∑ c : OrderedFinpartition n, stationaryPartitionWeight c :=
        (mul_sum _ _ _).symm
      _ ≤ (3 * (n + 1) ^ 2) * (3 ^ n * n.factorial ^ 2) := Nat.mul_le_mul_left _ ih
      _ = 3 ^ (n + 1) * (n + 1).factorial ^ 2 := by
        rw [pow_succ, Nat.factorial_succ]
        ring

end FalconerThetaGauge
