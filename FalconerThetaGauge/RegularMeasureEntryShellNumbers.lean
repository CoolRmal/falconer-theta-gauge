/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainNumbers

/-!
# Literal closing exponents of the induction and shell estimate

These are numerical consequences of `ParameterFacts`, with the exact `301`,
`0.378`, and `1/3` exponents from Section 9.3. No analytic energy bound is
assumed or asserted here.
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

/-- The entry jump and induction losses leave the literal gain `0.378β`. -/
theorem parameter_entry_shell_exponent {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    -(gain θ N) + 301 * blockParameter θ N + 12 * tolerance θ N + 2 / N ≤
      -(189 / 500) * gain θ N := by
  rcases hpar with ⟨hN₄, _, _, _, _, hκβ, hβsmall, _, hεκ, hsmall, _, _⟩
  have hκ := blockParameter_pos θ (by omega : 0 < N)
  have hκsmall : blockParameter θ N ≤ 1 / 10000 := hκβ.trans hβsmall
  have hεloss : 12 * tolerance θ N ≤ 5 * blockParameter θ N := by
    nlinarith
  linarith

/-- The two scalar terms after the entry jump fit below twice the surviving shell power. -/
theorem parameter_entry_shell_terms {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    (2 : ℝ) ^ ((N : ℝ) * (-(gain θ N) + 301 * blockParameter θ N +
      12 * tolerance θ N + 2 / N)) + (2 : ℝ) ^ (-80 * (N : ℝ)) ≤
        2 * (2 : ℝ) ^ (-(189 / 500) * gain θ N * N) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hβ := gain_pos θ hN
  have hβsmall := hpar.2.2.2.2.2.2.1
  have hβbound : gain θ N ≤ 1 / 20 := by linarith
  have hfirst := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_left (parameter_entry_shell_exponent hpar) hN')
  have hsecond := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_right (by linarith : (-80 : ℝ) ≤ -(189 / 500) * gain θ N) hN')
  have heq : (N : ℝ) * (-(189 / 500) * gain θ N) = -(189 / 500) * gain θ N * N := by ring
  rw [heq] at hfirst
  linarith

/-- The factor five in Section 9.3 is absorbed by the exact difference from `β/3`. -/
theorem parameter_five_times_shell_power {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    5 * (2 : ℝ) ^ (-(189 / 500) * gain θ N * N) ≤
      (2 : ℝ) ^ (-(gain θ N) * N / 3) := by
  have hβN := (parameter_gain_block_depth_margins hpar).1
  have hfactor : (5 : ℝ) ≤ (2 : ℝ) ^ ((67 / 1500) * gain θ N * N) := by
    calc
      _ ≤ (2 : ℝ) ^ (3 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  calc
    _ ≤ (2 : ℝ) ^ ((67 / 1500) * gain θ N * N) *
        (2 : ℝ) ^ (-(189 / 500) * gain θ N * N) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (-(gain θ N) * N / 3) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- The full scalar expression in Step 5 of Proposition 9.3 has the desired shell gain. -/
theorem parameter_shell_numeric_bound {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    2 * ((2 : ℝ) ^ ((N : ℝ) * (-(gain θ N) + 301 * blockParameter θ N +
      12 * tolerance θ N + 2 / N)) + (2 : ℝ) ^ (-80 * (N : ℝ))) +
        (2 : ℝ) ^ (-30 * (N : ℝ)) ≤ (2 : ℝ) ^ (-(gain θ N) * N / 3) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hβ := gain_pos θ hN
  have hβsmall := hpar.2.2.2.2.2.2.1
  have hβbound : gain θ N ≤ 1 / 20 := by linarith
  have herror := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_right (by linarith : (-30 : ℝ) ≤ -(189 / 500) * gain θ N)
      (Nat.cast_nonneg N))
  have hentry := parameter_entry_shell_terms hpar
  have hcombined : 2 * ((2 : ℝ) ^ ((N : ℝ) * (-(gain θ N) +
      301 * blockParameter θ N + 12 * tolerance θ N + 2 / N)) +
        (2 : ℝ) ^ (-80 * (N : ℝ))) + (2 : ℝ) ^ (-30 * (N : ℝ)) ≤
          5 * (2 : ℝ) ^ (-(189 / 500) * gain θ N * N) := by linarith
  exact hcombined.trans (parameter_five_times_shell_power hpar)

/-- The final leaf and accumulated-error scalar expression of Theorem 8.8 closes with `300κ`. -/
theorem parameter_energy_closing_bound {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    {V : ℝ} (hV : V ≤ 2) :
    2600 * (2 : ℝ) ^ ((N : ℝ) * (-V + 225 * blockParameter θ N)) +
      (2 : ℝ) ^ (-21 * (N : ℝ)) ≤
        (2 : ℝ) ^ ((N : ℝ) * (-V + 300 * blockParameter θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have hκN := (parameter_gain_block_depth_margins hpar).2
  have herror := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_right (by linarith : (-21 : ℝ) ≤ -V + 225 * blockParameter θ N)
      (Nat.cast_nonneg N))
  have hfactor : (2601 : ℝ) ≤ (2 : ℝ) ^ (75 * blockParameter θ N * N) := by
    calc
      _ ≤ (2 : ℝ) ^ (12 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  calc
    _ ≤ 2601 * (2 : ℝ) ^ ((N : ℝ) * (-V + 225 * blockParameter θ N)) := by
      have heq : (N : ℝ) * (-V + 225 * blockParameter θ N) =
          (-V + 225 * blockParameter θ N) * N := by ring
      rw [heq]
      linarith
    _ ≤ (2 : ℝ) ^ (75 * blockParameter θ N * N) *
        (2 : ℝ) ^ ((N : ℝ) * (-V + 225 * blockParameter θ N)) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end FalconerThetaGauge
