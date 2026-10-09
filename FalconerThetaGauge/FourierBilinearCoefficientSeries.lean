/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierBilinearCoefficientSum
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Coefficient Cauchy--Schwarz for the actual infinite separation expansion -/

@[expose] public section

noncomputable section

open Filter Finset

namespace FalconerThetaGauge

theorem summable_norm_mul_of_weighted_sq {ι : Type*} {c z : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hca : ∀ i, ‖c i‖ ≤ a i) (has : Summable a)
    (hazs : Summable (fun i ↦ a i * ‖z i‖ ^ 2)) :
    Summable (fun i ↦ ‖c i * z i‖) := by
  apply (has.add hazs).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro i
  have hnorm : ‖z i‖ ≤ 1 + ‖z i‖ ^ 2 := by nlinarith [sq_nonneg (‖z i‖ - 1)]
  calc
    _ = ‖c i‖ * ‖z i‖ := norm_mul _ _
    _ ≤ a i * ‖z i‖ := mul_le_mul_of_nonneg_right (hca i) (norm_nonneg _)
    _ ≤ a i * (1 + ‖z i‖ ^ 2) := mul_le_mul_of_nonneg_left hnorm (ha i)
    _ = _ := by ring

theorem norm_tsum_mul_sq_le_weighted {ι : Type*} {c z : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hca : ∀ i, ‖c i‖ ≤ a i) (has : Summable a)
    (hazs : Summable (fun i ↦ a i * ‖z i‖ ^ 2)) :
    ‖∑' i, c i * z i‖ ^ 2 ≤ (∑' i, a i) * ∑' i, a i * ‖z i‖ ^ 2 := by
  have hcz : Summable (fun i ↦ c i * z i) :=
    (summable_norm_mul_of_weighted_sq ha hca has hazs).of_norm
  exact le_of_tendsto_of_tendsto' (hcz.hasSum.norm.pow 2)
    (Tendsto.mul has.hasSum hazs.hasSum)
    (fun s ↦ norm_sum_mul_sq_le_weighted s c z (fun i _ ↦ hca i))

theorem norm_tsum_mul_add_sq_le_weighted {ι : Type*} {c z : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hca : ∀ i, ‖c i‖ ≤ a i) (has : Summable a)
    (hazs : Summable (fun i ↦ a i * ‖z i‖ ^ 2)) (e : ℂ) :
    ‖(∑' i, c i * z i) + e‖ ^ 2 ≤
      2 * (∑' i, a i) * (∑' i, a i * ‖z i‖ ^ 2) + 2 * ‖e‖ ^ 2 := by
  have hsum := norm_tsum_mul_sq_le_weighted ha hca has hazs
  have htri := norm_add_le (∑' i, c i * z i) e
  have hs := sq_nonneg (‖∑' i, c i * z i‖ - ‖e‖)
  have hp := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith

end FalconerThetaGauge
