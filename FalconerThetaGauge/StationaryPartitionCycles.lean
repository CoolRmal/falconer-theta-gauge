module

public import FalconerThetaGauge.StationaryPartitionWeights

/-! # The exact factorial sum of cyclic weights of the Faà di Bruno partitions -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

def stationaryPartitionCycleWeight {n : ℕ} (c : OrderedFinpartition n) : ℕ :=
  ∏ i, (c.partSize i - 1).factorial

theorem stationaryPartitionCycleWeight_extendLeft {n : ℕ} (c : OrderedFinpartition n) :
    stationaryPartitionCycleWeight c.extendLeft = stationaryPartitionCycleWeight c := by
  change (∏ x : Fin (c.length + 1),
    Nat.factorial ((Fin.cons (α := fun _ ↦ ℕ) 1 c.partSize) x - 1)) =
      ∏ i, (c.partSize i - 1).factorial
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.sub_self,
    Nat.factorial_zero, one_mul]

theorem stationaryPartitionCycleWeight_extendMiddle {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) :
    stationaryPartitionCycleWeight (c.extendMiddle i) = c.partSize i *
      stationaryPartitionCycleWeight c := by
  classical
  have hfun : (fun j ↦ ((Function.update c.partSize i (c.partSize i + 1)) j - 1).factorial) =
      Function.update (fun j ↦ (c.partSize j - 1).factorial) i (c.partSize i).factorial := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  change (∏ x : Fin c.length,
    Nat.factorial ((Function.update c.partSize i (c.partSize i + 1)) x - 1)) =
      c.partSize i * ∏ i, (c.partSize i - 1).factorial
  rw [hfun, prod_update_of_mem (mem_univ i), sdiff_singleton_eq_erase]
  have he : (c.partSize i).factorial = c.partSize i * (c.partSize i - 1).factorial := by
    have hh : c.partSize i = c.partSize i - 1 + 1 := by have := c.partSize_pos i; omega
    conv_lhs => rw [hh, Nat.factorial_succ]
    rw [← hh]
  rw [he, mul_assoc, mul_prod_erase univ (fun x ↦ (c.partSize x - 1).factorial) (mem_univ i)]

theorem stationaryPartitionCycleWeight_sum_extend {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Option (Fin c.length), stationaryPartitionCycleWeight (c.extend i) =
      (n + 1) * stationaryPartitionCycleWeight c := by
  classical
  rw [Fintype.sum_option]
  simp only [OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    stationaryPartitionCycleWeight_extendLeft, stationaryPartitionCycleWeight_extendMiddle]
  rw [← sum_mul, orderedFinpartition_sum_partSize]
  ring

/-- The exact cyclic partition sum is `n!`; no Bell-number overestimate is needed. -/
theorem sum_stationaryPartitionCycleWeight_eq (n : ℕ) :
    ∑ c : OrderedFinpartition n, stationaryPartitionCycleWeight c = n.factorial := by
  classical
  induction n with
  | zero => simp [stationaryPartitionCycleWeight, OrderedFinpartition.default_eq,
      OrderedFinpartition.atomic]
  | succ n ih =>
    have he : (∑ c : OrderedFinpartition (n + 1), stationaryPartitionCycleWeight c) =
        ∑ c : OrderedFinpartition n, ∑ i : Option (Fin c.length),
          stationaryPartitionCycleWeight (c.extend i) := by
      have h := (Fintype.sum_equiv (OrderedFinpartition.extendEquiv n)
        (fun p ↦ stationaryPartitionCycleWeight (p.1.extend p.2))
        stationaryPartitionCycleWeight (fun _ ↦ rfl)).symm
      simpa only [Fintype.sum_sigma] using h
    rw [he]
    simp_rw [stationaryPartitionCycleWeight_sum_extend]
    rw [← mul_sum, ih, Nat.factorial_succ]

end FalconerThetaGauge
