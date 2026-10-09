/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpatialInversePowerBinomial

/-! # The exact positive binomial sum and its sharp separation budget -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem choose_negative_half_mul_neg_pow (j m : ℕ) (q : ℝ) :
    Ring.choose (-(j : ℝ) / 2) m * (-q) ^ m =
      |Ring.choose (-(j : ℝ) / 2) m| * q ^ m := by
  have ha : (m : ℝ) - 1 ≤ (j : ℝ) / 2 + m - 1 := by
    linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hnonneg := real_choose_nonneg m ha
  have hneg : -(j : ℝ) / 2 = -((j : ℝ) / 2) := by ring
  rw [hneg, Ring.choose_neg, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow,
    abs_mul, abs_neg_one_zpow, one_mul, abs_of_nonneg hnonneg,
    zpow_natCast]
  have hs : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hqpow : (-q) ^ m = (-1 : ℝ) ^ m * q ^ m := by
    rw [← mul_pow]
    simp
  rw [hqpow]
  calc
    _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
        Ring.choose ((j : ℝ) / 2 + m - 1) m * q ^ m := by ring
    _ = _ := by rw [hs]; ring

theorem hasSum_inversePowerBinomial_abs (j : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hqsmall : q < 1) :
    HasSum (fun m : ℕ ↦ |Ring.choose (-(j : ℝ) / 2) m| * q ^ m)
      ((1 - q) ^ (-(j : ℝ) / 2)) := by
  have hs := hasSum_inversePowerBinomial j
    (show |-q| < 1 by rwa [abs_neg, abs_of_nonneg hq])
  simpa only [choose_negative_half_mul_neg_pow, sub_eq_add_neg] using hs

theorem tsum_inversePowerBinomial_abs_le_sqrt (j : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hqsmall : q ≤ 1 / 4) :
    (∑' m : ℕ, |Ring.choose (-(j : ℝ) / 2) m| * q ^ m) ≤ (Real.sqrt 2) ^ j := by
  rw [(hasSum_inversePowerBinomial_abs j hq (by linarith)).tsum_eq]
  have h := Real.rpow_le_rpow_of_nonpos
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (1 / 2 : ℝ) ≤ 1 - q)
    (show -(j : ℝ) / 2 ≤ 0 by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j])
  calc
    _ ≤ (1 / 2 : ℝ) ^ (-(j : ℝ) / 2) := h
    _ = (2 : ℝ) ^ ((j : ℝ) / 2) := by
      have he : -(j : ℝ) / 2 = -((j : ℝ) / 2) := by ring
      rw [one_div, Real.inv_rpow (by norm_num), he, Real.rpow_neg (by norm_num), inv_inv]
    _ = (Real.sqrt 2) ^ j := by
      rw [Real.rpow_div_two_eq_sqrt _ (by norm_num), Real.rpow_natCast]

end FalconerThetaGauge
