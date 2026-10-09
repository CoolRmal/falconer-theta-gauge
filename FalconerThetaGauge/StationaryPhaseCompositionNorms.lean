module

public import FalconerThetaGauge.StationaryPartitionCycles
public import FalconerThetaGauge.StationaryGevreyComposition
public import FalconerThetaGauge.StationaryPhaseOperatorsComplex

/-! # Actual weighted coefficient sums for the circular Morse composition -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_stationaryMorseAngle_cycle_le (m : ℕ) (hm : 0 < m)
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedDeriv m stationaryMorseAngle s‖ ≤ 2 ^ m * ((m - 1).factorial : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h := norm_iteratedDeriv_stationaryMorseAngle_succ_le j hs
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ,
    mul_assoc, mul_comm, mul_left_comm] using h

def stationaryCompositionWeightedNorm (m n : ℕ) (M : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), ‖stationaryCompositionCoefficient m k‖ * M ^ k

/-- The literal real composition coefficients have an analytic factorial bound. -/
theorem stationaryCompositionWeightedNorm_le {m n : ℕ} (hmn : m ≤ n)
    {M : ℝ} (hM : 1 ≤ M) :
    stationaryCompositionWeightedNorm m n M ≤ (2 * M) ^ m * (m.factorial : ℝ) := by
  classical
  have hM0 : 0 ≤ M := by linarith
  have hterm (c : OrderedFinpartition m) :
      (∏ r, ‖iteratedDeriv (c.partSize r) stationaryMorseAngle 0‖) * M ^ c.length ≤
        (2 * M) ^ m * (stationaryPartitionCycleWeight c : ℝ) := by
    have hp : (∏ r, ‖iteratedDeriv (c.partSize r) stationaryMorseAngle 0‖) ≤
        2 ^ m * ∏ r, ((c.partSize r - 1).factorial : ℝ) := by
      calc
        _ ≤ ∏ r, 2 ^ c.partSize r * ((c.partSize r - 1).factorial : ℝ) := by
          apply prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          intro r _
          exact norm_iteratedDeriv_stationaryMorseAngle_cycle_le _ (c.partSize_pos r)
            (by norm_num)
        _ = _ := by
          rw [prod_mul_distrib, prod_pow_eq_pow_sum, orderedFinpartition_sum_partSize]
    calc
      _ ≤ (2 ^ m * ∏ r, ((c.partSize r - 1).factorial : ℝ)) * M ^ c.length :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg hM0 _)
      _ ≤ (2 ^ m * ∏ r, ((c.partSize r - 1).factorial : ℝ)) * M ^ m := by
        gcongr
        exact c.length_le
      _ = _ := by simp only [stationaryPartitionCycleWeight, Nat.cast_prod, mul_pow]; ring
  unfold stationaryCompositionWeightedNorm
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        (∑ c : OrderedFinpartition m,
          ‖if c.length = k then ∏ r, iteratedDeriv (c.partSize r) stationaryMorseAngle 0
            else 0‖) * M ^ k := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hM0 _)
    _ = ∑ c : OrderedFinpartition m,
        (∏ r, ‖iteratedDeriv (c.partSize r) stationaryMorseAngle 0‖) * M ^ c.length := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro c _
      have hc : c.length ∈ range (n + 1) := mem_range.mpr (by have := c.length_le; omega)
      rw [sum_eq_single_of_mem c.length hc]
      · simp only [ite_true, norm_prod]
      · intro b _ hb
        simp [Ne.symm hb]
    _ ≤ ∑ c : OrderedFinpartition m,
        (2 * M) ^ m * (stationaryPartitionCycleWeight c : ℝ) :=
      sum_le_sum (fun c _ ↦ hterm c)
    _ = _ := by
      rw [← mul_sum, ← Nat.cast_sum, sum_stationaryPartitionCycleWeight_eq]

end FalconerThetaGauge
