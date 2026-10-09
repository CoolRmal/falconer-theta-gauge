/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierBilinearCauchySchwarz
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # The actual scalar coefficient Cauchy--Schwarz inequality for finite Fourier expansions -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

theorem norm_sum_mul_sq_le_weighted {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    {a : ι → ℝ} (ha : ∀ i ∈ s, ‖c i‖ ≤ a i) :
    ‖∑ i ∈ s, c i * z i‖ ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * ‖z i‖ ^ 2 := by
  have ha₀ : ∀ i ∈ s, 0 ≤ a i := fun i hi ↦ (norm_nonneg _).trans (ha i hi)
  have hb : ‖∑ i ∈ s, c i * z i‖ ≤ ∑ i ∈ s, a i * ‖z i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖c i * z i‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg _)
  calc
    _ ≤ (∑ i ∈ s, a i * ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ ≤ _ := sum_sq_le_sum_mul_sum_of_sq_le_mul s ha₀
      (fun i hi ↦ mul_nonneg (ha₀ i hi) (sq_nonneg _))
      (fun i _ ↦ le_of_eq (by ring))

theorem norm_sum_mul_add_sq_le_weighted {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    {a : ι → ℝ} (ha : ∀ i ∈ s, ‖c i‖ ≤ a i) (e : ℂ) :
    ‖(∑ i ∈ s, c i * z i) + e‖ ^ 2 ≤
      2 * (∑ i ∈ s, a i) * (∑ i ∈ s, a i * ‖z i‖ ^ 2) + 2 * ‖e‖ ^ 2 := by
  have hsum := norm_sum_mul_sq_le_weighted s c z ha
  have htri := norm_add_le (∑ i ∈ s, c i * z i) e
  have hs := sq_nonneg (‖∑ i ∈ s, c i * z i‖ - ‖e‖)
  have hp := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith

end FalconerThetaGauge
