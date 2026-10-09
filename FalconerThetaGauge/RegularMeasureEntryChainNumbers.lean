/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainBudget

/-!
# Literal numerical losses in the finite induction

The logarithmic branch budget absorbs the actual node count and repeated
factor `320`. The rounded tolerance pays the `13ε` loss at every ordinary
move. All estimates use the literal constants of the manuscript.
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

/-- A logarithmic budget absorbs a real power into a power of two. -/
theorem rpow_le_two_rpow_of_log_budget {B x y : ℝ} (hB : 0 < B)
    (hbudget : x * (Real.log B / Real.log 2) ≤ y) : B ^ x ≤ (2 : ℝ) ^ y := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← mul_div_assoc] at hbudget
  have h := (div_le_iff₀ hlog).mp hbudget
  rw [Real.rpow_def_of_pos hB, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The parameter budget gives the explicit depth margins used to absorb fixed constants. -/
theorem parameter_gain_block_depth_margins {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    200 ≤ gain θ N * N ∧ 80 ≤ blockParameter θ N * N := by
  rcases hpar with ⟨hN₄, _, _, ⟨hbranch, hlog⟩, _, _, _, _, _, hgain, _, _⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hκ := blockParameter_pos θ (by omega : 0 < N)
  have hε := tolerance_pos θ (by omega : 0 < N)
  have hgain' := (div_le_iff₀ hN).mp hgain
  have hcoeff : (2 : ℝ) ≤ 7 / blockParameter θ N + 1 / tolerance θ N + 2 := by
    have h₁ : 0 ≤ 7 / blockParameter θ N := by positivity
    have h₂ : 0 ≤ 1 / tolerance θ N := by positivity
    linarith
  have hproduct := mul_le_mul hcoeff hlog (by norm_num) (by positivity)
  constructor <;> nlinarith

/-- The exact ordinary-move multiplier loss `13ε · 7/κ` is at most `κ`. -/
theorem parameter_ordinary_multiplier_loss {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    13 * tolerance θ N * (7 / blockParameter θ N) ≤ blockParameter θ N := by
  rcases hpar with ⟨hN₄, _, _, _, _, _, _, _, hε, _, _, _⟩
  have hκ := blockParameter_pos θ (by omega : 0 < N)
  have heq : 13 * tolerance θ N * (7 / blockParameter θ N) =
      91 * tolerance θ N / blockParameter θ N := by ring
  rw [heq]
  apply (div_le_iff₀ hκ).mpr
  nlinarith [sq_nonneg (blockParameter θ N)]

/-- The inverse-tolerance factor in (P3) separately pays for repeated fixed multipliers. -/
theorem parameter_inverse_tolerance_log_budget {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    10 / tolerance θ N ≤ blockParameter θ N * N / 4 := by
  rcases hpar with ⟨hN₄, _, _, ⟨hbranch, hlog⟩, _, _, _, _, _, _, _, _⟩
  have hκ := blockParameter_pos θ (by omega : 0 < N)
  have hε := tolerance_pos θ (by omega : 0 < N)
  have hcoeff : 1 / tolerance θ N ≤ 7 / blockParameter θ N + 1 / tolerance θ N + 2 := by
    have hpos : 0 ≤ 7 / blockParameter θ N := by positivity
    linarith
  calc
    10 / tolerance θ N = (1 / tolerance θ N) * 10 := by ring
    _ ≤ (1 / tolerance θ N) * (Real.log ((N : ℝ) + 16) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (7 / blockParameter θ N + 1 / tolerance θ N + 2) *
        (Real.log ((N : ℝ) + 16) / Real.log 2) :=
      mul_le_mul_of_nonneg_right hcoeff (by linarith)
    _ ≤ _ := hbranch

/-- The repeated low-frequency constant `C₁ = 320` costs at most `R^κ`. -/
theorem parameter_lowFrequency_constant_bound {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    (320 : ℝ) ^ (1 / tolerance θ N) ≤ (2 : ℝ) ^ (blockParameter θ N * N) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have hε := tolerance_pos θ hN
  have hbudget := parameter_inverse_tolerance_log_budget hpar
  have hbase : (320 : ℝ) ≤ (2 : ℝ) ^ (10 : ℝ) := by norm_num
  calc
    _ ≤ ((2 : ℝ) ^ (10 : ℝ)) ^ (1 / tolerance θ N) :=
      Real.rpow_le_rpow (by norm_num) hbase (by positivity)
    _ = (2 : ℝ) ^ (10 / tolerance θ N) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (blockParameter θ N * N / 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by
        have : 0 ≤ blockParameter θ N * N := by positivity
        linarith)

/-- The literal branch-factor power in Section 8.5 is absorbed by `R^κ`. -/
theorem parameter_tree_node_bound {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    ((N : ℝ) + 14) ^ (7 / blockParameter θ N + 1 / tolerance θ N + 1) ≤
      (2 : ℝ) ^ (blockParameter θ N * N) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have hε := tolerance_pos θ hN
  have hbranch := hpar.2.2.2.1.1
  have hpow := rpow_le_two_rpow_of_log_budget (by positivity : (0 : ℝ) < N + 16) hbranch
  calc
    _ ≤ ((N : ℝ) + 16) ^ (7 / blockParameter θ N + 1 / tolerance θ N + 1) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ ≤ ((N : ℝ) + 16) ^ (7 / blockParameter θ N + 1 / tolerance θ N + 2) :=
      Real.rpow_le_rpow_of_exponent_le
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by linarith)
    _ ≤ (2 : ℝ) ^ (blockParameter θ N * N / 4) := hpow
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by
        have : 0 ≤ blockParameter θ N * N := by positivity
        linarith)

/-- The fixed near and far multipliers fit below the ordinary `13ε` loss. -/
theorem parameter_near_far_constant_bound {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    (81 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (13 * tolerance θ N * N) ∧
      (2 : ℝ) ^ (90 : ℝ) ≤ (2 : ℝ) ^ (13 * tolerance θ N * N) := by
  have hεN := hpar.2.2.1.1
  have hbase : (81 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (90 : ℝ) := by norm_num
  have hfar := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by nlinarith : (90 : ℝ) ≤ 13 * tolerance θ N * N)
  exact ⟨hbase.trans hfar, hfar⟩

/-- The literal leaf prefactor is absorbed by `R^κ`. -/
theorem parameter_leaf_constant_bound {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    (2600 : ℝ) ≤ (2 : ℝ) ^ (blockParameter θ N * N) := by
  have hmargin := (parameter_gain_block_depth_margins hpar).2
  calc
    _ ≤ (2 : ℝ) ^ (80 : ℝ) := by norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hmargin

end FalconerThetaGauge
