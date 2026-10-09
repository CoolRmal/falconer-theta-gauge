module

public import FalconerThetaGauge.ExplicitBumpCutoff
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The manuscript's actual polynomial derivative base for angular cutoffs -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem factorial_cast_le_cutoff_order_pow {T k : ℕ} (hk : k ≤ 6 * T) :
    (k.factorial : ℝ) ≤ (6 * (T : ℝ)) ^ k := by
  have h : k.factorial ≤ (6 * T) ^ k :=
    (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hk k)
  exact_mod_cast h

theorem explicitDerivativeConstant_le_polynomial_base {T k : ℕ} (hT : 2 ≤ T)
    (hk : k ≤ 6 * T) :
    (Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2 ≤ ((4 * (T : ℝ)) ^ 3) ^ k := by
  have hT' : 2 ≤ (T : ℝ) := by exact_mod_cast hT
  have hp : 0 ≤ Real.pi ^ 2 / 6 := by positivity
  have hpi : Real.pi ^ 2 / 6 ≤ 3 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hf := factorial_cast_le_cutoff_order_pow hk
  calc
    _ ≤ 3 ^ k * ((6 * (T : ℝ)) ^ k) ^ 2 := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ hp hpi k
      · exact pow_le_pow_left₀ (by positivity) hf 2
      · positivity
      · positivity
    _ = (3 * (6 * (T : ℝ)) ^ 2) ^ k := by
      rw [mul_pow 3 ((6 * (T : ℝ)) ^ 2) k, ← pow_mul, ← pow_mul, Nat.mul_comm k 2]
    _ ≤ ((4 * (T : ℝ)) ^ 3) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      have hsq : 0 ≤ (T : ℝ) ^ 2 := sq_nonneg _
      have hmul := mul_nonneg (show 0 ≤ 64 * (T : ℝ) - 108 by linarith) hsq
      nlinarith

/-- All derivatives through `6T` obey the exact base used in source (3.12) and (6.6). -/
theorem norm_iteratedDeriv_explicitPassingMask_le_polynomial_base {T : ℕ} (hT : 2 ≤ T)
    {k : ℕ} (hk : k ≤ 6 * T) {δ : ℝ} (hδ : 0 < δ) (Z : Set ℝ) (x : ℝ) :
    ‖iteratedDeriv k (explicitPassingMask (6 * T) δ Z) x‖ ≤
      ((4 * (T : ℝ)) ^ 3 / δ) ^ k := by
  calc
    _ ≤ δ⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) :=
      norm_iteratedDeriv_explicitPassingMask_le (6 * T) k hk hδ Z x
    _ ≤ δ⁻¹ ^ k * ((4 * (T : ℝ)) ^ 3) ^ k :=
      mul_le_mul_of_nonneg_left (explicitDerivativeConstant_le_polynomial_base hT hk)
        (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; simp only [div_eq_mul_inv, mul_comm]

end FalconerThetaGauge
