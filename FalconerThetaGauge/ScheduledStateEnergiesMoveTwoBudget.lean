module

public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwoOrthogonality

/-! # The literal `640` multiplier and high-shell errors fit Move 2's source budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

theorem moveTwo_high_multiplier_le {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (k : ℝ) :
    640 * (2 : ℝ) ^ (N * (k + 12 * tolerance θ N)) ≤
      (2 : ℝ) ^ (N * (k + 13 * tolerance θ N)) := by
  have hsmall : (640 : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) := by
    exact (by norm_num : (640 : ℝ) ≤ (2 : ℝ) ^ (16 : ℝ)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hpar.2.2.1.1)
  calc
    _ ≤ (2 : ℝ) ^ (tolerance θ N * N) *
        (2 : ℝ) ^ (N * (k + 12 * tolerance θ N)) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem moveTwo_high_shell_error_le {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    640 * (toleranceCount θ N : ℝ) * (2 : ℝ) ^ (-(80 * (N : ℝ))) +
        320 * (toleranceCount θ N : ℝ) * (2 : ℝ) ^ (-(390 * (N : ℝ))) ≤
      (2 : ℝ) ^ (-(25 * (N : ℝ))) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hpar.1
  have hδ : (toleranceCount θ N : ℝ) ≤ N := by
    rw [← tolerance_mul_scale θ hN]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (parameterFacts_tolerance_le_one hpar) (Nat.cast_nonneg N)
  have hpow : (N : ℝ) ≤ (2 : ℝ) ^ (N : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.le_of_lt (show N < 2 ^ N from Nat.lt_two_pow_self))
  have hsmall : (2 : ℝ) ^ (-(390 * (N : ℝ))) ≤ (2 : ℝ) ^ (-(80 * (N : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    _ ≤ 960 * (toleranceCount θ N : ℝ) * (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
      have hh := mul_le_mul_of_nonneg_left hsmall
        (by positivity : 0 ≤ 320 * (toleranceCount θ N : ℝ))
      linarith
    _ ≤ (2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (N : ℝ) *
        (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
      have hconst : (960 : ℝ) ≤ (2 : ℝ) ^ (10 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hconst (hδ.trans hpow) (Nat.cast_nonneg _) (by positivity))
        (by positivity)
    _ = (2 : ℝ) ^ (10 - 79 * (N : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end FalconerThetaGauge
