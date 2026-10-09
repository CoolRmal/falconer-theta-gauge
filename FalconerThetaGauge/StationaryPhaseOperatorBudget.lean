module

public import FalconerThetaGauge.StationaryPhaseWeightedNorms

/-! # The literal numerical operator budget of circular stationary phase -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem stationary_operator_linear_factor_le (j : ℕ) (hj : 1 ≤ j) :
    2 * (2 * j + 1) ≤ 25 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst j; norm_num
    · have hh : 1 ≤ j := by omega
      calc
        _ ≤ 25 * (2 * (2 * j + 1)) := by omega
        _ ≤ 25 * 25 ^ j := Nat.mul_le_mul_left _ (ih hh)
        _ = _ := by rw [pow_succ]; omega

theorem factorial_double_le_factorial_mul_power (j : ℕ) :
    (2 * j).factorial ≤ j.factorial * (2 * j) ^ j := by
  have h := Nat.mul_le_mul_left j.factorial (Nat.ascFactorial_le_pow_add j j)
  rw [Nat.factorial_mul_ascFactorial] at h
  simpa only [← two_mul] using h

/-- The manuscript's `(100 j M²)^j` bound for the actual universal operators. -/
theorem stationaryPhaseWeightedNorm_le {j : ℕ} (hj : 1 ≤ j) {M : ℝ} (hM : 1 ≤ M) :
    stationaryPhaseWeightedNorm j M ≤ (100 * j * M ^ 2) ^ j := by
  have hjfact : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfactor : (2 * (2 * j + 1) : ℝ) ≤ 25 ^ j := by
    exact_mod_cast stationary_operator_linear_factor_le j hj
  have hfact : ((2 * j).factorial : ℝ) ≤ (j.factorial : ℝ) * (2 * j : ℝ) ^ j := by
    exact_mod_cast factorial_double_le_factorial_mul_power j
  rw [stationaryPhaseWeightedNorm_eq]
  calc
    _ ≤ (2 : ℝ)⁻¹ ^ j / (j.factorial : ℝ) *
        (2 * (2 * j + 1) * ((2 * j).factorial : ℝ) * (2 * M) ^ (2 * j)) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          stationaryDerivativeWeightedNorm_le (2 * j) hM) (by positivity)
    _ ≤ (2 : ℝ)⁻¹ ^ j / (j.factorial : ℝ) *
        (2 * (2 * j + 1) * ((j.factorial : ℝ) * (2 * j : ℝ) ^ j) *
          (2 * M) ^ (2 * j)) := by gcongr
    _ = (2 * (2 * j + 1)) * (4 * j * M ^ 2) ^ j := by
      rw [pow_mul]
      have he : (2 * M) ^ 2 = 4 * M ^ 2 := by ring
      rw [he, mul_pow, mul_pow]
      field_simp
      have htwo : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
      linear_combination ((j : ℝ) ^ j * M ^ (j * 2) * 4 ^ j) * htwo
    _ ≤ 25 ^ j * (4 * j * M ^ 2) ^ j :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end FalconerThetaGauge
