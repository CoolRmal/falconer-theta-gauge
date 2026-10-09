module

public import FalconerThetaGauge.StationaryPhaseOperatorBudget

/-! # The factorial budget in the actual circular stationary remainder -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem factorial_double_add_two_le (T : ℕ) :
    (2 * T + 2).factorial ≤ (2 * T + 2) ^ 2 * (2 * T).factorial := by
  rw [show 2 * T + 2 = (2 * T + 1) + 1 by omega, Nat.factorial_succ,
    Nat.factorial_succ]
  nlinarith [Nat.factorial_pos (2 * T)]

/-- The exact factorial loss is cubic in the truncation order inside the power. -/
theorem factorial_double_add_two_sq_le (T : ℕ) :
    ((2 * T + 2).factorial : ℝ) ^ 2 / (T.factorial : ℝ) ≤
      (2 * (T : ℝ) + 2) ^ 4 * (4 * (T : ℝ) ^ 3) ^ T := by
  have hfac : 0 < (T.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos T
  have hstep : ((2 * T + 2).factorial : ℝ) ≤
      (2 * (T : ℝ) + 2) ^ 2 * ((2 * T).factorial : ℝ) := by
    exact_mod_cast factorial_double_add_two_le T
  have hdouble : ((2 * T).factorial : ℝ) ≤
      (T.factorial : ℝ) * (2 * (T : ℝ)) ^ T := by
    exact_mod_cast factorial_double_le_factorial_mul_power T
  have hT : (T.factorial : ℝ) ≤ (T : ℝ) ^ T := by
    exact_mod_cast Nat.factorial_le_pow T
  calc
    _ ≤ ((2 * (T : ℝ) + 2) ^ 2 * ((T.factorial : ℝ) * (2 * (T : ℝ)) ^ T)) ^ 2 /
        (T.factorial : ℝ) := by
      gcongr
      exact hstep.trans (mul_le_mul_of_nonneg_left hdouble (by positivity))
    _ = (2 * (T : ℝ) + 2) ^ 4 * (T.factorial : ℝ) * ((2 * (T : ℝ)) ^ 2) ^ T := by
      have hpow : ((2 * (T : ℝ)) ^ T) ^ 2 = ((2 * (T : ℝ)) ^ 2) ^ T := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm T 2]
      rw [mul_pow, mul_pow, hpow]
      field_simp
    _ ≤ (2 * (T : ℝ) + 2) ^ 4 * (T : ℝ) ^ T * ((2 * (T : ℝ)) ^ 2) ^ T := by
      gcongr
    _ = _ := by
      rw [mul_assoc, ← mul_pow]
      congr 2
      ring

end FalconerThetaGauge
