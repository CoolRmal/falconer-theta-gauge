/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # The actual binomial series used to separate inverse distances -/

@[expose] public section

noncomputable section

open Finset Polynomial

namespace FalconerThetaGauge

private theorem real_choose_eq_descPochhammer (a : ℝ) (n : ℕ) :
    Ring.choose a n = (n.factorial : ℝ)⁻¹ * (descPochhammer ℝ n).eval a := by
  rw [Ring.choose_eq_smul, smul_eq_mul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval, descPochhammer_eval_eq_ascPochhammer]

theorem real_choose_nonneg {a : ℝ} (n : ℕ) (ha : (n : ℝ) - 1 ≤ a) :
    0 ≤ Ring.choose a n := by
  rw [real_choose_eq_descPochhammer]
  exact mul_nonneg (by positivity) (descPochhammer_nonneg ha)

theorem real_choose_mono {a b : ℝ} (n : ℕ) (ha : (n : ℝ) - 1 ≤ a) (hab : a ≤ b) :
    Ring.choose a n ≤ Ring.choose b n := by
  rw [real_choose_eq_descPochhammer, real_choose_eq_descPochhammer]
  exact mul_le_mul_of_nonneg_left
    (monotoneOn_descPochhammer_eval n ha (ha.trans hab) hab) (by positivity)

theorem abs_choose_negative_half_le (j m : ℕ) :
    |Ring.choose (-(j : ℝ) / 2) m| ≤ (2 : ℝ) ^ (j + m) := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have ha : (m : ℝ) - 1 ≤ (j : ℝ) / 2 + m - 1 := by linarith
  have hnonneg := real_choose_nonneg m ha
  have hmono := real_choose_mono m ha
    (show (j : ℝ) / 2 + m - 1 ≤ (j + m : ℕ) by push_cast; linarith)
  have hbound : Ring.choose ((j + m : ℕ) : ℝ) m ≤ (2 : ℝ) ^ (j + m) := by
    rw [Ring.choose_natCast]
    exact_mod_cast Nat.choose_le_two_pow (j + m) m
  have hneg : -(j : ℝ) / 2 = -((j : ℝ) / 2) := by ring
  rw [hneg, Ring.choose_neg, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow, abs_mul,
    abs_neg_one_zpow, one_mul, abs_of_nonneg hnonneg]
  exact hmono.trans hbound

theorem hasSum_inversePowerBinomial (j : ℕ) {s : ℝ} (hs : |s| < 1) :
    HasSum (fun m : ℕ ↦ Ring.choose (-(j : ℝ) / 2) m * s ^ m)
      ((1 + s) ^ (-(j : ℝ) / 2)) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := -(j : ℝ) / 2)).hasSum (y := s)
    (by simpa only [← ENNReal.ofReal_one, Metric.eball_ofReal, Metric.mem_ball,
      dist_zero_right, Real.norm_eq_abs] using hs)
  simpa only [binomialSeries_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul, zero_add] using h

theorem summable_inversePowerBinomial_abs (j : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hqsmall : q ≤ 1 / 4) :
    Summable (fun m : ℕ ↦ |Ring.choose (-(j : ℝ) / 2) m| * q ^ m) := by
  have hdom : Summable (fun m : ℕ ↦ (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ m) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  apply hdom.of_nonneg_of_le (fun m ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hq _))
  intro m
  calc
    _ ≤ (2 : ℝ) ^ (j + m) * (1 / 4 : ℝ) ^ m := by
      exact mul_le_mul (abs_choose_negative_half_le j m)
        (pow_le_pow_left₀ hq hqsmall m) (pow_nonneg hq m) (by positivity)
    _ = _ := by rw [pow_add, mul_assoc, ← mul_pow]; norm_num

theorem tsum_inversePowerBinomial_abs_le (j : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hqsmall : q ≤ 1 / 4) :
    (∑' m : ℕ, |Ring.choose (-(j : ℝ) / 2) m| * q ^ m) ≤ 2 * (2 : ℝ) ^ j := by
  have hs := summable_inversePowerBinomial_abs j hq hqsmall
  have hdom : Summable (fun m : ℕ ↦ (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ m) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  calc
    _ ≤ ∑' m : ℕ, (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ m := by
      apply Summable.tsum_le_tsum _ hs hdom
      intro m
      calc
        _ ≤ (2 : ℝ) ^ (j + m) * (1 / 4 : ℝ) ^ m :=
          mul_le_mul (abs_choose_negative_half_le j m)
            (pow_le_pow_left₀ hq hqsmall m) (pow_nonneg hq m) (by positivity)
        _ = _ := by rw [pow_add, mul_assoc, ← mul_pow]; norm_num
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num)]; norm_num; ring

end FalconerThetaGauge
