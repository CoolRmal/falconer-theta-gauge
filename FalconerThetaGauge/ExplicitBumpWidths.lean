module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The explicit box widths and their exact factorial product

The finite-order smoothing construction uses the manuscript's widths
`6/(π² j²)`. Every finite partial sum leaves a positive radius for the smooth
tail, while the first `k` signed differences cost exactly `(π²/6)^k (k!)²`.
-/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

def explicitBoxWidth (j : ℕ) : ℝ := 6 / (Real.pi ^ 2 * (j + 1 : ℝ) ^ 2)

theorem explicitBoxWidth_pos (j : ℕ) : 0 < explicitBoxWidth j := by
  unfold explicitBoxWidth
  positivity

theorem explicitBoxWidth_inv (j : ℕ) :
    (explicitBoxWidth j)⁻¹ = (Real.pi ^ 2 / 6) * (j + 1 : ℝ) ^ 2 := by
  unfold explicitBoxWidth
  field_simp

theorem prod_explicitBoxWidth_inv (k : ℕ) :
    (∏ j ∈ range k, (explicitBoxWidth j)⁻¹) = (Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, explicitBoxWidth_inv, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem hasSum_explicitBoxWidth : HasSum explicitBoxWidth 1 := by
  have hshift := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at hshift
  have h := hshift.mul_left (6 / Real.pi ^ 2)
  convert h using 1
  · funext j
    unfold explicitBoxWidth
    field_simp
  · field_simp

theorem sum_explicitBoxWidth_lt_one (K : ℕ) : ∑ j ∈ range K, explicitBoxWidth j < 1 := by
  have h := hasSum_explicitBoxWidth.summable.sum_le_tsum (range (K + 1))
    (fun j _ ↦ (explicitBoxWidth_pos j).le)
  rw [hasSum_explicitBoxWidth.tsum_eq, sum_range_succ] at h
  linarith [explicitBoxWidth_pos K]

/-- Every finite box convolution leaves genuine room for an arbitrary smooth tail. -/
def explicitBumpTailRadius (K : ℕ) : ℝ := 1 - ∑ j ∈ range K, explicitBoxWidth j

theorem explicitBumpTailRadius_pos (K : ℕ) : 0 < explicitBumpTailRadius K := by
  unfold explicitBumpTailRadius
  linarith [sum_explicitBoxWidth_lt_one K]

end FalconerThetaGauge
