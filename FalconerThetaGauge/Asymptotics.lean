module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Summability and the scale threshold

These estimates justify the asymptotic costs in Section 2 and the summability
step in Section 9 of the source manuscript. They do not assume the geometric
shell-energy estimate needed for Theorem 1.1.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace FalconerThetaGauge

/-- Every positive power eventually dominates the logarithm with any fixed
positive coefficient. -/
theorem eventually_log_le_mul_rpow (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_atTop hs).bound hc
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [hn, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hnpos),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)] using hn

/-- A fixed additive shift in the logarithm does not change power domination. -/
theorem eventually_log_add_le_mul_rpow (s c : ℝ) (a : ℕ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + a) ≤ c * (n : ℝ) ^ s := by
  have hp := ((tendsto_rpow_atTop hs).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop (by positivity : 0 < c / 2)
  filter_upwards [eventually_log_le_mul_rpow s (c / 2) hs (by positivity),
    hp.eventually (eventually_ge_atTop (Real.log 2)),
    eventually_ge_atTop a, eventually_ge_atTop 1] with n hlog hconst hna hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hna' : (a : ℝ) ≤ n := by exact_mod_cast hna
  dsimp only [Function.comp_def] at hconst
  have hmono : Real.log ((n : ℝ) + a) ≤ Real.log (2 * n) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hmono
  linarith

/-- The branch-counting exponent is positive precisely above the manuscript's
two-thirds threshold. -/
theorem branchExponent_pos_iff (θ : ℝ) : 0 < 3 * θ - 2 ↔ 2 / 3 < θ := by
  constructor <;> intro h <;> linarith

/-- The cost involving the logarithm is absorbed by the positive power
`n^(3θ-2)` in the range of Theorem 1.1. -/
theorem eventually_branchCost (θ c : ℝ) (hθ : 2 / 3 < θ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) ^ (3 * θ - 2) :=
  eventually_log_le_mul_rpow _ c ((branchExponent_pos_iff θ).2 hθ) hc

/-- A stretched exponential beats any inverse-square bound eventually. -/
theorem eventually_exp_neg_mul_rpow_le (θ c : ℝ) (hθ : 0 < θ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * (n : ℝ) ^ θ) ≤ (n : ℝ) ^ (-2 : ℝ) := by
  filter_upwards [eventually_log_le_mul_rpow θ (c / 2) hθ (by positivity),
    eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  rw [Real.rpow_def_of_pos hnpos (-2)]
  apply Real.exp_le_exp.mpr
  linarith

/-- Summability of the shell-energy decay asserted in Section 9. -/
theorem summable_exp_neg_mul_nat_rpow (θ c : ℝ) (hθ : 0 < θ) (hc : 0 < c) :
    Summable (fun n : ℕ ↦ Real.exp (-c * (n : ℝ) ^ θ)) := by
  apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  apply IsBigO.of_bound 1
  filter_upwards [eventually_exp_neg_mul_rpow_le θ c hθ hc] with n hn
  simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (-2))] using hn

/-- The filter error modeled by `(ε_N N)^(-8)` is summable in the whole
claimed parameter range, since `ε_N N` has order `N^(2θ-1)`. -/
theorem summable_filter_power (θ : ℝ) (hθ : 2 / 3 < θ) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ (-8 * (2 * θ - 1))) := by
  apply Real.summable_nat_rpow.mpr
  linarith

end FalconerThetaGauge
