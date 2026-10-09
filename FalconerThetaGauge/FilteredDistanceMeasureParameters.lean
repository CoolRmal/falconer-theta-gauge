module

public import FalconerThetaGauge.FilteredDistanceMeasureTests
public import FalconerThetaGauge.ParameterBudgets
public import FalconerThetaGauge.FilterSummability
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The exact scale-dependent filter loss and its summability

The logarithmic cutoff budget follows from the actual parameter facts of
Lemma 2.2. The full error `a_N` retains the rounded block and tolerance
parameters and all constants in Lemma 6.13.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped ENNReal

namespace FalconerThetaGauge

/-- The actual parameter budget (P1) implies the cutoff budget used in Lemma 6.13. -/
theorem ParameterFacts.filter_log_budget {θ : ℝ} {N : ℕ} (h : ParameterFacts θ N) :
    Real.log (2 * Real.pi * ((N : ℝ) ^ 2 + 1)) ≤
      (2 * Real.log 2 - 1) * (tolerance θ N * N) := by
  have hbase : 1 ≤ (N : ℝ) + 16 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpow : ((N : ℝ) + 16) ^ (2 : ℕ) ≤ ((N : ℝ) + 16) ^ (12 : ℕ) :=
    pow_le_pow_right₀ hbase (by norm_num)
  have hT : 1 ≤ ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (expansionCount θ N)])
  have hcoef : (8 : ℝ) ≤ (2 : ℝ) ^ (80 : ℕ) *
      ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) := by
    nlinarith
  have hπ : 2 * Real.pi * ((N : ℝ) ^ 2 + 1) ≤
      8 * ((N : ℝ) ^ 2 + 1) := by
    exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (by positivity)
  have hpoly : 2 * Real.pi * ((N : ℝ) ^ 2 + 1) ≤
      (2 : ℝ) ^ (80 : ℕ) * ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) := by
    calc
      _ ≤ 8 * ((N : ℝ) ^ 2 + 1) := hπ
      _ ≤ 8 * ((N : ℝ) + 16) ^ (12 : ℕ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hl := Real.log_le_log (by positivity : 0 < 2 * Real.pi * ((N : ℝ) ^ 2 + 1))
    (hpoly.trans h.2.1)
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hl
  have hc : Real.log 2 / 8 ≤ 2 * Real.log 2 - 1 := by
    linarith [Real.log_two_gt_d9]
  have hE : 0 ≤ tolerance θ N * N := by linarith [h.2.2.1.1]
  exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_right hc hE])

/-- The literal real bound `a_N` in Lemma 6.13. -/
def weightedFilterMassError (θ K : ℝ) (N : ℕ) : ℝ :=
  (21 / 10 : ℝ) *
    (4 * (2 : ℝ) ^ (-(blockParameter θ N * N) / 4) +
      2 * (3 * (N + 1 : ℝ) * (2 : ℝ) ^ (-(tolerance θ N * N)) +
        (2 : ℝ) ^ 8 * K * (tolerance θ N * N) ^ (-8 : ℝ)))

theorem tolerance_mul_scale_nonneg (θ : ℝ) (N : ℕ) : 0 ≤ tolerance θ N * N := by
  unfold tolerance
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem weightedFilterMassError_nonneg {θ K : ℝ} (hK : 0 ≤ K) (N : ℕ) :
    0 ≤ weightedFilterMassError θ K N := by
  have he := tolerance_mul_scale_nonneg θ N
  unfold weightedFilterMassError
  positivity

/-- The `N+1` factor of the literal source error is summable at the rounded tolerance. -/
theorem summable_dyadic_tolerance_error_add_one (θ : ℝ) (hθ : 1 / 2 < θ) :
    Summable (fun N : ℕ ↦ (N + 1 : ℝ) * (2 : ℝ) ^ (-(tolerance θ N * N))) := by
  apply summable_of_isBigO_nat (summable_dyadic_tolerance_error θ hθ)
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hadd : 0 ≤ (N + 1 : ℝ) := by linarith
  have hexp : 0 ≤ (2 : ℝ) ^ (-(tolerance θ N * N)) := Real.rpow_nonneg (by norm_num) _
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hadd hexp),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) hexp)]
  nlinarith

/-- The complete literal removed-mass bound is summable in the claimed range. -/
theorem summable_weightedFilterMassError (θ K : ℝ) (hθ : 2 / 3 < θ) :
    Summable (weightedFilterMassError θ K) := by
  have hb := (summable_dyadic_block_error θ (by linarith)).mul_left 4
  have he := (summable_dyadic_tolerance_error_add_one θ (by linarith)).mul_left 3
  have hp := (summable_rounded_filter_error θ hθ).mul_left ((2 : ℝ) ^ 8 * K)
  have hs := (hb.add ((he.add hp).mul_left 2)).mul_left (21 / 10 : ℝ)
  convert hs using 1
  ext N
  dsimp [weightedFilterMassError]
  ring

/-- The literal ENNReal bound in Lemma 6.13 agrees with `ofReal a_N`. -/
theorem weightedFilterMassError_ofReal (θ : ℝ) {K : ℝ} (hK : 0 ≤ K) (N : ℕ) :
    ENNReal.ofReal (weightedFilterMassError θ K N) = ENNReal.ofReal (21 / 10) *
      (ENNReal.ofReal (2 * (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)) +
        ENNReal.ofReal (2 * (2 : ℝ) ^ (-(blockParameter θ N * N) / 4)) +
        2 * radialFilterCost N (tolerance θ N * N) (ENNReal.ofReal K)) := by
  have he := tolerance_mul_scale_nonneg θ N
  unfold weightedFilterMassError radialFilterCost
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 21 / 10),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [ENNReal.ofReal_ofNat]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ 8 * K),
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ) ^ 8)]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 2
  · congr 1
    ring
  · rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ) ^ 8)]
    rw [mul_right_comm (ENNReal.ofReal ((2 : ℝ) ^ 8)) (ENNReal.ofReal K)]

end FalconerThetaGauge
