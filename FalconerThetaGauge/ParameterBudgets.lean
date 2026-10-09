module

public import FalconerThetaGauge.Parameters

/-!
# Explicit eventual parameter budgets

These inequalities use the rounded parameters of Definition 2.1. In particular,
the logarithmic branch budget is proved at the terminal scale itself.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace FalconerThetaGauge

/-- The rounded block parameter is eventually at most any positive constant. -/
theorem eventually_blockParameter_le (θ c : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hc : 0 < c) : ∀ᶠ N : ℕ in atTop, blockParameter θ N ≤ c := by
  have hgain := (tendsto_gain_zero θ hθ₁).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 500 * c))
  filter_upwards [eventually_blockParameter_le_gain_div θ hθ₀, hgain] with N hk hg
  linarith

/-- At a small block parameter, the branch-count coefficient is controlled
by one inverse square. -/
theorem branch_count_coefficient_le {κ ε : ℝ} (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hε : κ ^ 2 / 1000000 ≤ ε) :
    (7 / κ + 1 / ε + 2) * κ ^ 2 ≤ 1000009 := by
  have hεpos : 0 < ε := lt_of_lt_of_le (by positivity) hε
  have he : 1 / ε * κ ^ 2 ≤ 1000000 := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hεpos).mpr
    linarith
  have hseven : 7 / κ * κ ^ 2 = 7 * κ := by field_simp
  have hsquare : κ ^ 2 ≤ 1 := by nlinarith
  calc
    (7 / κ + 1 / ε + 2) * κ ^ 2 = 7 * κ + 1 / ε * κ ^ 2 + 2 * κ ^ 2 := by
      rw [add_mul, add_mul, hseven]
    _ ≤ 1000009 := by linarith

/-- The first inequality of (P3), including the precise fixed scale shift. -/
theorem eventually_logarithmic_branch_budget (θ : ℝ) (hθ₀ : 2 / 3 < θ)
    (hθ₁ : θ < 1) : ∀ᶠ N : ℕ in atTop,
    (7 / blockParameter θ N + 1 / tolerance θ N + 2) *
      (Real.log ((N : ℝ) + 16) / Real.log 2) ≤ blockParameter θ N * N / 4 := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / (4 * 1000009) := by positivity
  filter_upwards [eventually_log_add_le_blockParameter_cube_mul_scale θ
    (Real.log 2 / (4 * 1000009)) 16 hθ₀ hc,
    eventually_blockParameter_le θ 1 (by linarith) hθ₁ (by norm_num),
    eventually_ge_atTop 1] with N hlog hk hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hκ := blockParameter_pos θ hNpos
  have hε := tolerance_pos θ hNpos
  have hcoeff := branch_count_coefficient_le hκ hk
    (blockParameter_sq_div_le_tolerance θ hNpos)
  have hcoeffpos : 0 ≤ 7 / blockParameter θ N + 1 / tolerance θ N + 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hcoeffpos
  have hprod := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ Real.log 2 / (4 * 1000009) * blockParameter θ N * N by positivity)
  have heq :
      (7 / blockParameter θ N + 1 / tolerance θ N + 2) *
        (Real.log 2 / (4 * 1000009) * blockParameter θ N ^ 3 * N) =
      ((7 / blockParameter θ N + 1 / tolerance θ N + 2) * blockParameter θ N ^ 2) *
        (Real.log 2 / (4 * 1000009) * blockParameter θ N * N) := by ring
  rw [heq] at hmul
  have hbound :
      (7 / blockParameter θ N + 1 / tolerance θ N + 2) * Real.log ((N : ℝ) + 16) ≤
        blockParameter θ N * N / 4 * Real.log 2 := by
    have := hmul.trans hprod
    convert this using 1
    ring
  simpa only [mul_div_assoc] using (div_le_iff₀ hlogtwo).mpr hbound

/-- The mask-level ceiling fits inside the expansion ceiling at the small
parameter values used in (P4). -/
theorem maskLevelCount_le_expansionCount_of_small_parameters
    (θ : ℝ) {N : ℕ} (hN : 0 < N) (hκ₁ : blockParameter θ N ≤ 1)
    (hε : tolerance θ N ≤ blockParameter θ N ^ 2 / 500000) :
    maskLevelCount θ N ≤ expansionCount θ N := by
  have hκ := blockParameter_pos θ hN
  have htol := tolerance_pos θ hN
  have hsquare : blockParameter θ N ^ 2 ≤ blockParameter θ N := by nlinarith
  have htolκ : tolerance θ N ≤ blockParameter θ N / 500000 := by linarith
  have htolone : tolerance θ N ≤ 1 / 500000 := by linarith
  have hdiv : 7 / blockParameter θ N * tolerance θ N ≤ 7 / 500000 := by
    have h : tolerance θ N / blockParameter θ N ≤ 1 / 500000 :=
      (div_le_iff₀ hκ).mpr (by linarith)
    convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 7) using 1 <;> ring
  have hbound : 7 / blockParameter θ N + 1 / tolerance θ N + 3 ≤
      240 / tolerance θ N := by
    apply (le_div_iff₀ htol).mpr
    have heq : (7 / blockParameter θ N + 1 / tolerance θ N + 3) * tolerance θ N =
        7 / blockParameter θ N * tolerance θ N + 1 + 3 * tolerance θ N := by
      field_simp
    rw [heq]
    linarith
  unfold maskLevelCount expansionCount
  rw [← Nat.ceil_add_natCast (by positivity :
    0 ≤ 7 / blockParameter θ N + 1 / tolerance θ N) 3]
  exact Nat.ceil_mono (by simpa using hbound)

/-- The mask count fits within the expansion order for all sufficiently large
terminal scales. -/
theorem eventually_maskLevelCount_le_expansionCount (θ : ℝ) (hθ₀ : 2 / 3 < θ)
    (hθ₁ : θ < 1) :
    ∀ᶠ N : ℕ in atTop, maskLevelCount θ N ≤ expansionCount θ N := by
  filter_upwards [eventually_blockParameter_le θ 1 (by linarith) hθ₁ (by norm_num),
    eventually_tolerance_le_blockParameter_sq_div θ (by linarith),
    eventually_ge_atTop 1] with N hk he hN
  exact maskLevelCount_le_expansionCount_of_small_parameters θ
    (lt_of_lt_of_le Nat.zero_lt_one hN) hk he

/-- The terminal-scale correction in (P4) is absorbed by the gain. -/
theorem eventually_two_div_scale_le_gain_div (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, 2 / (N : ℝ) ≤ gain θ N / 100 := by
  filter_upwards [(tendsto_gain_mul_scale_atTop θ hθ).eventually
    (eventually_ge_atTop 200), eventually_ge_atTop 1] with N hgain hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  exact (div_le_iff₀ hNpos).mpr (by linarith)

/-- The final chain-counting inequality in (P4) holds at the actual rounded
block length. -/
theorem eventually_chain_count_budget (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, 2 * (1 / blockParameter θ N + 2) * (N + 1) ≤ (N : ℝ) ^ 2 := by
  have hp := tendsto_blockParameter_pow_mul_scale_atTop θ 1 (by simpa using hθ)
  filter_upwards [hp.eventually (eventually_ge_atTop 16),
    eventually_ge_atTop 16] with N hlarge hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 16) hN
  have hκ := blockParameter_pos θ hNpos
  have hNreal : (16 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [pow_one] at hlarge
  have hinv : 1 / blockParameter θ N ≤ (N : ℝ) / 16 :=
    (div_le_iff₀ hκ).mpr (by nlinarith)
  have hbound := mul_le_mul_of_nonneg_right hinv (show 0 ≤ (N : ℝ) + 1 by positivity)
  nlinarith

/-- All the inequalities grouped as (P4) in Lemma 2.2 hold simultaneously. -/
theorem eventually_parameter_facts_P4 (θ : ℝ) (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) :
    ∀ᶠ N : ℕ in atTop,
      gain θ N / 1000 ≤ blockParameter θ N ∧
      blockParameter θ N ≤ gain θ N / 500 ∧
      gain θ N / 500 ≤ 1 / 10000 ∧
      blockParameter θ N ^ 2 / 1000000 ≤ tolerance θ N ∧
      tolerance θ N ≤ blockParameter θ N ^ 2 / 500000 ∧
      2 / (N : ℝ) ≤ gain θ N / 100 ∧
      maskLevelCount θ N ≤ expansionCount θ N ∧
      2 * (1 / blockParameter θ N + 2) * (N + 1) ≤ (N : ℝ) ^ 2 := by
  have hgain := (tendsto_gain_zero θ hθ₁).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
  filter_upwards [eventually_blockParameter_le_gain_div θ (by linarith), hgain,
    eventually_tolerance_le_blockParameter_sq_div θ (by linarith),
    eventually_two_div_scale_le_gain_div θ (by linarith),
    eventually_maskLevelCount_le_expansionCount θ hθ₀ hθ₁,
    eventually_chain_count_budget θ (by linarith),
    eventually_ge_atTop 1] with N hk hg he hn hi hc hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  exact ⟨gain_div_le_blockParameter θ hNpos, hk, by linarith,
    blockParameter_sq_div_le_tolerance θ hNpos, he, hn, hi, hc⟩

/-- The second inequality of (P3) is eventually satisfied. -/
theorem eventually_logarithmic_scale_ge_ten :
    ∀ᶠ N : ℕ in atTop, 10 ≤ Real.log ((N : ℝ) + 16) / Real.log 2 := by
  filter_upwards [eventually_ge_atTop 1024] with N hN
  have hNreal : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hmono : Real.log ((2 : ℝ) ^ (10 : ℕ)) ≤ Real.log ((N : ℝ) + 16) :=
    Real.log_le_log (by positivity) (by norm_num; linarith)
  rw [Real.log_pow] at hmono
  norm_num only [Nat.cast_ofNat] at hmono
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact hmono

/-- Both branch-counting facts (P3) hold at one common eventual scale. -/
theorem eventually_parameter_facts_P3 (θ : ℝ) (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) :
    ∀ᶠ N : ℕ in atTop,
      (7 / blockParameter θ N + 1 / tolerance θ N + 2) *
        (Real.log ((N : ℝ) + 16) / Real.log 2) ≤ blockParameter θ N * N / 4 ∧
      10 ≤ Real.log ((N : ℝ) + 16) / Real.log 2 :=
  (eventually_logarithmic_branch_budget θ hθ₀ hθ₁).and
    eventually_logarithmic_scale_ge_ten

/-- The non-polynomial regular-part count is bounded by one inverse tolerance. -/
theorem regular_part_count_le {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤
      (49 / Real.log 2 + 2997 / 100) / ε := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := div_le_div_of_nonneg_right
    (Real.log_le_self (by positivity : (0 : ℝ) ≤ 49 / ε)) hlogtwo.le
  have hone : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hlinear := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 333 / 100)
  have heq : (49 / Real.log 2 + 2997 / 100) / ε =
      (49 / ε) / Real.log 2 + (333 / 100) * (8 / ε + 1 / ε) := by ring
  rw [heq]
  linarith

/-- The regular-part count inequality of (P2) holds above the two-thirds
threshold with the actual rounded tolerance. -/
theorem eventually_regular_part_budget (θ : ℝ) (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) :
    ∀ᶠ N : ℕ in atTop, Real.log (49 / tolerance θ N) / Real.log 2 +
      (333 / 100 : ℝ) * (8 / tolerance θ N + 1) ≤ blockParameter θ N * N / 4 := by
  let C : ℝ := 49 / Real.log 2 + 2997 / 100
  have hC : 0 < C := by
    have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C]
    positivity
  have hp := tendsto_blockParameter_pow_mul_scale_atTop θ 3
    (by norm_num only [Nat.cast_ofNat]; linarith)
  filter_upwards [hp.eventually (eventually_ge_atTop (4 * C * 1000000)),
    eventually_parameter_facts_P4 θ hθ₀ hθ₁,
    eventually_blockParameter_le θ 1 (by linarith) hθ₁ (by norm_num),
    eventually_ge_atTop 1] with N hlarge hP4 hk hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hκ := blockParameter_pos θ hNpos
  have hε := tolerance_pos θ hNpos
  have hε₁ : tolerance θ N ≤ 1 := by
    have hsquare : blockParameter θ N ^ 2 ≤ 1 := by nlinarith
    linarith [hP4.2.2.2.2.1]
  have hinv := one_div_le_one_div_of_le
    (by positivity : 0 < blockParameter θ N ^ 2 / 1000000)
    (blockParameter_sq_div_le_tolerance θ hNpos)
  have hcount := regular_part_count_le hε hε₁
  have hupper : C / tolerance θ N ≤ C * 1000000 / blockParameter θ N ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hinv hC.le
    convert h using 1 <;> ring
  have hbudget : C * 1000000 / blockParameter θ N ^ 2 ≤ blockParameter θ N * N / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hκ)).mpr
    nlinarith
  exact hcount.trans (hupper.trans hbudget)

/-- Both regular-part facts (P2) hold simultaneously. -/
theorem eventually_parameter_facts_P2 (θ : ℝ) (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) :
    ∀ᶠ N : ℕ in atTop,
      16 ≤ tolerance θ N * N ∧
      Real.log (49 / tolerance θ N) / Real.log 2 +
        (333 / 100 : ℝ) * (8 / tolerance θ N + 1) ≤ blockParameter θ N * N / 4 :=
  ((tendsto_tolerance_mul_scale_atTop θ (by linarith)).eventually
    (eventually_ge_atTop 16)).and (eventually_regular_part_budget θ hθ₀ hθ₁)

/-- Positivity of the integer tolerance numerator gives a coarse polynomial
bound on the expansion order, uniformly in the exponent. -/
theorem expansionCount_add_one_le_scale (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    (expansionCount θ N : ℝ) + 1 ≤ 242 * N := by
  have hκ := blockParameter_pos θ hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < toleranceCount θ N := Nat.ceil_pos.mpr (by positivity)
  have hmass : (1 : ℝ) ≤ tolerance θ N * N := by
    rw [tolerance_mul_scale θ hN]
    exact_mod_cast hc
  have hε := tolerance_pos θ hN
  have hinv : 1 / tolerance θ N ≤ (N : ℝ) := (div_le_iff₀ hε).mpr (by nlinarith)
  have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 240 / tolerance θ N)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold expansionCount
  have heq : 240 / tolerance θ N = 240 * (1 / tolerance θ N) := by ring
  rw [heq]
  rw [heq] at hceil
  linarith

/-- The derivative and polynomial constants are absorbed by the stretched
exponential gain in (P1). -/
theorem eventually_parameter_fact_P1 (θ : ℝ) (hθ : 1 / 2 < θ) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ (80 : ℕ) * ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) ≤
      (2 : ℝ) ^ (tolerance θ N * N / 8) := by
  let c : ℝ := (gainCoefficient θ / 1000) ^ 2 / 1000000
  let A : ℝ := 80 * Real.log 2 + 12 * Real.log 242
  have hc : 0 < c := by
    have := gainCoefficient_pos θ
    dsimp [c]
    positivity
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := ((tendsto_rpow_atTop (by linarith : 0 < 2 * θ - 1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop
    (by positivity : 0 < c * Real.log 2 / 16)
  filter_upwards [hp.eventually (eventually_ge_atTop A),
    eventually_log_add_le_mul_rpow (2 * θ - 1) (c * Real.log 2 / 384) 16
      (by linarith) (by positivity), eventually_ge_atTop 1] with N hconst hlog hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  dsimp only [Function.comp_def] at hconst
  have hlower := tolerance_mul_scale_lower θ hNpos
  have hsum : A + 24 * Real.log ((N : ℝ) + 16) ≤
      tolerance θ N * N / 8 * Real.log 2 := by
    have hmult := mul_le_mul_of_nonneg_right hlower hlogtwo.le
    dsimp [c] at hconst hlog
    linarith
  have hT := expansionCount_add_one_le_scale θ hNpos
  have hpow : ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) ≤
      (242 * ((N : ℝ) + 16)) ^ (12 : ℕ) := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hpoly : (2 : ℝ) ^ (80 : ℕ) * ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) *
      ((N : ℝ) + 16) ^ (12 : ℕ) ≤
      (2 : ℝ) ^ (80 : ℕ) * (242 : ℝ) ^ (12 : ℕ) * ((N : ℝ) + 16) ^ (24 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (2 : ℝ) ^ (80 : ℕ)))
      (show 0 ≤ ((N : ℝ) + 16) ^ (12 : ℕ) by positivity)
    convert h using 1
    ring
  have hexp : (2 : ℝ) ^ (80 : ℕ) * (242 : ℝ) ^ (12 : ℕ) *
      ((N : ℝ) + 16) ^ (24 : ℕ) = Real.exp (A + 24 * Real.log ((N : ℝ) + 16)) := by
    dsimp [A]
    simp only [Real.exp_add]
    rw [show (80 : ℝ) = (80 : ℕ) by norm_num, Real.exp_nat_mul,
      show (12 : ℝ) = (12 : ℕ) by norm_num, Real.exp_nat_mul,
      show (24 : ℝ) = (24 : ℕ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 242), Real.exp_log (by positivity)]
  calc
    (2 : ℝ) ^ (80 : ℕ) * ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) ≤
        (2 : ℝ) ^ (80 : ℕ) * (242 : ℝ) ^ (12 : ℕ) * ((N : ℝ) + 16) ^ (24 : ℕ) := hpoly
    _ = Real.exp (A + 24 * Real.log ((N : ℝ) + 16)) := hexp
    _ ≤ Real.exp (tolerance θ N * N / 8 * Real.log 2) := Real.exp_le_exp.mpr hsum
    _ = (2 : ℝ) ^ (tolerance θ N * N / 8) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- The four quantitative groups in Lemma 2.2, with `R^(ε/8)` written as
`2^(εN/8)` and every decimal constant represented by its exact rational value. -/
def ParameterFacts (θ : ℝ) (N : ℕ) : Prop :=
  4 ≤ N ∧
  (2 : ℝ) ^ (80 : ℕ) * ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) *
    ((N : ℝ) + 16) ^ (12 : ℕ) ≤ (2 : ℝ) ^ (tolerance θ N * N / 8) ∧
  (16 ≤ tolerance θ N * N ∧
    Real.log (49 / tolerance θ N) / Real.log 2 +
      (333 / 100 : ℝ) * (8 / tolerance θ N + 1) ≤ blockParameter θ N * N / 4) ∧
  ((7 / blockParameter θ N + 1 / tolerance θ N + 2) *
      (Real.log ((N : ℝ) + 16) / Real.log 2) ≤ blockParameter θ N * N / 4 ∧
    10 ≤ Real.log ((N : ℝ) + 16) / Real.log 2) ∧
  (gain θ N / 1000 ≤ blockParameter θ N ∧
    blockParameter θ N ≤ gain θ N / 500 ∧
    gain θ N / 500 ≤ 1 / 10000 ∧
    blockParameter θ N ^ 2 / 1000000 ≤ tolerance θ N ∧
    tolerance θ N ≤ blockParameter θ N ^ 2 / 500000 ∧
    2 / (N : ℝ) ≤ gain θ N / 100 ∧
    maskLevelCount θ N ≤ expansionCount θ N ∧
    2 * (1 / blockParameter θ N + 2) * (N + 1) ≤ (N : ℝ) ^ 2)

/-- Lemma 2.2: the full four groups of scale-dependent parameter facts hold
above one threshold depending only on the exponent. -/
theorem exists_parameter_threshold (θ : ℝ) (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) :
    ∃ Npar : ℕ, ∀ N ≥ Npar, ParameterFacts θ N := by
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop 4, eventually_parameter_fact_P1 θ (by linarith),
    eventually_parameter_facts_P2 θ hθ₀ hθ₁,
    eventually_parameter_facts_P3 θ hθ₀ hθ₁,
    eventually_parameter_facts_P4 θ hθ₀ hθ₁] with N hN hP1 hP2 hP3 hP4
  exact ⟨hN, hP1, hP2, hP3, hP4⟩

end FalconerThetaGauge
