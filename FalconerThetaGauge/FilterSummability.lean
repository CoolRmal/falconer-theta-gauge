module

public import FalconerThetaGauge.Parameters
public import FalconerThetaGauge.GaugeLogEnergy

/-!
# Summability of the actual removed-mass errors

All three terms in the scale-dependent filter bound are summable: the rounded
tolerance power, the terminal-scale polynomial times the tolerance exponential,
and the block exponential. No geometric removed-mass estimate is assumed here.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics

namespace FalconerThetaGauge

/-- Every positive stretched-exponential block power is summable, with the
rounded block parameter retained. -/
theorem summable_exp_neg_block_power (θ c : ℝ) (k : ℕ) (hc : 0 < c)
    (hexp : 0 < (θ - 1) * k + 1) :
    Summable (fun N : ℕ ↦ Real.exp (-c * blockParameter θ N ^ k * N)) := by
  have ha : 0 < (gainCoefficient θ / 1000) ^ k :=
    pow_pos (div_pos (gainCoefficient_pos θ) (by norm_num)) k
  apply summable_of_isBigO_nat
    (summable_exp_neg_mul_nat_rpow ((θ - 1) * k + 1)
      (c * (gainCoefficient θ / 1000) ^ k) hexp (mul_pos hc ha))
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hlower := blockParameter_pow_mul_scale_lower θ k
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hbound : Real.exp (-c * blockParameter θ N ^ k * N) ≤
      Real.exp (-(c * (gainCoefficient θ / 1000) ^ k) *
        (N : ℝ) ^ ((θ - 1) * k + 1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] using hbound

/-- The manuscript's `R^(-κ/4)` term is summable. -/
theorem summable_dyadic_block_error (θ : ℝ) (hθ : 0 < θ) :
    Summable (fun N : ℕ ↦ (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := summable_exp_neg_block_power θ (Real.log 2 / 4) 1
    (by positivity) (by simpa using hθ)
  convert hs using 1
  ext N
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [pow_one]
  congr 1
  ring

/-- The manuscript's `N R^(-ε)` term is summable for every exponent above one half. -/
theorem summable_dyadic_tolerance_error (θ : ℝ) (hθ : 1 / 2 < θ) :
    Summable (fun N : ℕ ↦ (N : ℝ) * (2 : ℝ) ^ (-(tolerance θ N * N))) := by
  let c : ℝ := (gainCoefficient θ / 1000) ^ 2 / 1000000
  have hc : 0 < c := by
    have := gainCoefficient_pos θ
    dsimp [c]
    positivity
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := GaugeLogEnergy.summable_pow_mul_exp_neg 1 (2 * θ - 1)
    (Real.log 2 * c) (by norm_num) (by linarith) (mul_pos hlogtwo hc)
  simp only [Real.rpow_one] at hs
  apply summable_of_isBigO_nat hs
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hlower := tolerance_mul_scale_lower θ (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hexp : (2 : ℝ) ^ (-(tolerance θ N * N)) ≤
      Real.exp (-(Real.log 2 * c) * (N : ℝ) ^ (2 * θ - 1)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    dsimp [c]
    nlinarith
  have hbound := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa only [Real.norm_eq_abs, one_mul,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.exp_pos _).le)] using hbound

/-- The three actual error terms in the filter's removed-mass estimate. -/
def filterMassError (θ : ℝ) (N : ℕ) : ℝ :=
  (tolerance θ N * N) ^ (-8 : ℝ) +
    (N : ℝ) * (2 : ℝ) ^ (-(tolerance θ N * N)) +
    (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)

/-- Their summability is proved at the exact scale-dependent parameters. -/
theorem summable_filterMassError (θ : ℝ) (hθ : 2 / 3 < θ) :
    Summable (filterMassError θ) :=
  ((summable_rounded_filter_error θ hθ).add
    (summable_dyadic_tolerance_error θ (by linarith))).add
      (summable_dyadic_block_error θ (by linarith))

end FalconerThetaGauge
