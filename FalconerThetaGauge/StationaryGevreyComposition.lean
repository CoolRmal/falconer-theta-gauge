module

public import FalconerThetaGauge.StationaryPartitionWeights
public import FalconerThetaGauge.ComplexMorseJacobian

/-! # Actual finite order Gevrey composition bounds -/

@[expose] public section

noncomputable section

open Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_stationaryMorseAngle_le (m : ℕ) (hm : 0 < m)
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedDeriv m stationaryMorseAngle s‖ ≤ 2 ^ m * (m.factorial : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  calc
    _ ≤ 2 * (j.factorial : ℝ) * 2 ^ j :=
      norm_iteratedDeriv_stationaryMorseAngle_succ_le j hs
    _ ≤ 2 ^ (j + 1) * ((j + 1).factorial : ℝ) := by
      have hh : (j.factorial : ℝ) ≤ ((j + 1).factorial : ℝ) :=
        by exact_mod_cast Nat.factorial_le (Nat.le_succ j)
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]

theorem orderedFinpartition_prod_factorial_le {n : ℕ} (c : OrderedFinpartition n) :
    ∏ i, (c.partSize i).factorial ≤ n.factorial := by
  have hd := Nat.prod_factorial_dvd_factorial_sum univ c.partSize
  rw [orderedFinpartition_sum_partSize] at hd
  exact Nat.le_of_dvd (Nat.factorial_pos n) hd

/-- The finite Faà di Bruno sum gives a uniform bound for an actual composition. -/
theorem norm_iteratedDeriv_comp_le_gevrey
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ} {g : ℝ → E} {n : ℕ} {x A B C : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g (f x))
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hfderiv : ∀ m, 0 < m → m ≤ n →
      ‖iteratedDeriv m f x‖ ≤ C ^ m * (m.factorial : ℝ))
    (hgderiv : ∀ k, k ≤ n →
      ‖iteratedDeriv k g (f x)‖ ≤ A * B ^ k * (k.factorial : ℝ) ^ 2) :
    ‖iteratedDeriv n (g ∘ f) x‖ ≤ A * (3 * B * C) ^ n * (n.factorial : ℝ) ^ 2 := by
  classical
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hf le_rfl]
  have hterm (c : OrderedFinpartition n) :
      ‖(∏ r, iteratedDeriv (c.partSize r) f x) • iteratedDeriv c.length g (f x)‖ ≤
        (A * B ^ n * C ^ n) * (stationaryPartitionWeight c : ℝ) := by
    have hp : (∏ r, ‖iteratedDeriv (c.partSize r) f x‖) ≤
        C ^ n * ∏ r, ((c.partSize r).factorial : ℝ) := by
      calc
        _ ≤ ∏ r, C ^ (c.partSize r) * ((c.partSize r).factorial : ℝ) := by
          apply prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          intro r _
          exact hfderiv _ (c.partSize_pos r) (c.partSize_le r)
        _ = _ := by
          rw [prod_mul_distrib, prod_pow_eq_pow_sum, orderedFinpartition_sum_partSize]
    have hb : B ^ c.length ≤ B ^ n := pow_le_pow_right₀ hB c.length_le
    rw [norm_smul, norm_prod]
    calc
      _ ≤ (C ^ n * ∏ r, ((c.partSize r).factorial : ℝ)) *
          (A * B ^ c.length * (c.length.factorial : ℝ) ^ 2) :=
        mul_le_mul hp (hgderiv _ c.length_le) (norm_nonneg _)
          (mul_nonneg (pow_nonneg hC _) (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _))
      _ ≤ (C ^ n * ∏ r, ((c.partSize r).factorial : ℝ)) *
          (A * B ^ n * (c.length.factorial : ℝ) ^ 2) := by
        gcongr
      _ = _ := by
        simp only [stationaryPartitionWeight, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
        ring
  calc
    _ ≤ ∑ c : OrderedFinpartition n,
        ‖(∏ r, iteratedDeriv (c.partSize r) f x) • iteratedDeriv c.length g (f x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition n,
        (A * B ^ n * C ^ n) * (stationaryPartitionWeight c : ℝ) :=
      sum_le_sum (fun c _ ↦ hterm c)
    _ = (A * B ^ n * C ^ n) *
        ((∑ c : OrderedFinpartition n, stationaryPartitionWeight c : ℕ) : ℝ) := by
      rw [← mul_sum, Nat.cast_sum]
    _ ≤ (A * B ^ n * C ^ n) * (3 ^ n * (n.factorial : ℝ) ^ 2) := by
      gcongr
      exact_mod_cast sum_stationaryPartitionWeight_le n
    _ = _ := by rw [mul_pow, mul_pow]; ring

end FalconerThetaGauge
