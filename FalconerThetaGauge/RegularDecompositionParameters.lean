/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionInterpolation

/-!
# Exact rounded schedule for regular decomposition

The block length, bucket width and number of blocks retain the floor and ceiling
operations in Lemma 5.8. The numerical bounds hold at each terminal scale.
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

/-- The sampled-depth block length `Δ = floor(εN/4)`. -/
def regularDecompositionBlockLength (ε : ℝ) (N : ℕ) : ℕ := ⌊ε * N / 4⌋₊

/-- The logarithmic mass-bucket width `w = floor(εN/8)`. -/
def regularDecompositionBucketWidth (ε : ℝ) (N : ℕ) : ℕ := ⌊ε * N / 8⌋₊

/-- The number of sampled-depth blocks `k = ceil(N/Δ)`. -/
def regularDecompositionBlockCount (ε : ℝ) (N : ℕ) : ℕ :=
  ⌈(N : ℝ) / regularDecompositionBlockLength ε N⌉₊

theorem regularDecomposition_rounding_bounds {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) :
    ε * N / 8 ≤ regularDecompositionBlockLength ε N ∧
      (regularDecompositionBlockLength ε N : ℝ) ≤ ε * N / 4 ∧
      ε * N / 16 ≤ regularDecompositionBucketWidth ε N ∧
      (regularDecompositionBucketWidth ε N : ℝ) ≤ ε * N / 8 := by
  have hdlo := Nat.lt_floor_add_one (ε * N / 4)
  have hdhi := Nat.floor_le (by linarith : 0 ≤ ε * N / 4)
  have hwlo := Nat.lt_floor_add_one (ε * N / 8)
  have hwhi := Nat.floor_le (by linarith : 0 ≤ ε * N / 8)
  change ε * N / 4 < regularDecompositionBlockLength ε N + 1 at hdlo
  change (regularDecompositionBlockLength ε N : ℝ) ≤ ε * N / 4 at hdhi
  change ε * N / 8 < regularDecompositionBucketWidth ε N + 1 at hwlo
  change (regularDecompositionBucketWidth ε N : ℝ) ≤ ε * N / 8 at hwhi
  exact ⟨by linarith, hdhi, by linarith, hwhi⟩

theorem regularDecomposition_bucketWidth_pos {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) : 0 < regularDecompositionBucketWidth ε N := by
  have hbound := (regularDecomposition_rounding_bounds hεN).2.2.1
  have hreal : (0 : ℝ) < regularDecompositionBucketWidth ε N := by linarith
  exact_mod_cast hreal

theorem regularDecomposition_blockLength_pos {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) : 0 < regularDecompositionBlockLength ε N := by
  have hbound := (regularDecomposition_rounding_bounds hεN).1
  have hreal : (0 : ℝ) < regularDecompositionBlockLength ε N := by linarith
  exact_mod_cast hreal

/-- The dyadic branching exponent fits in eight mass buckets. -/
theorem regularDecomposition_branching_exponent_le {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) :
    2 * regularDecompositionBlockLength ε N ≤ 8 * regularDecompositionBucketWidth ε N := by
  obtain ⟨_, hdhi, hwlo, _⟩ := regularDecomposition_rounding_bounds hεN
  have hreal : 2 * (regularDecompositionBlockLength ε N : ℝ) ≤
      8 * regularDecompositionBucketWidth ε N := by linarith
  exact_mod_cast hreal

/-- The number of sampled blocks is bounded by the literal coefficient `8/ε+1`. -/
theorem regularDecomposition_blockCount_le {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hεN : 16 ≤ ε * N) : (regularDecompositionBlockCount ε N : ℝ) ≤ 8 / ε + 1 := by
  have hd : (0 : ℝ) < regularDecompositionBlockLength ε N :=
    Nat.cast_pos.mpr (regularDecomposition_blockLength_pos hεN)
  have hround := (regularDecomposition_rounding_bounds hεN).1
  have hratio : (N : ℝ) / regularDecompositionBlockLength ε N ≤ 8 / ε := by
    apply (div_le_iff₀ hd).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ (N : ℝ) / regularDecompositionBlockLength ε N by positivity)
  exact hceil.le.trans (by linarith)

/-- The exact terminal mass-class count is at most `48/ε+1`. -/
theorem regularDecomposition_terminalClassCount_le {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hεN : 16 ≤ ε * N) :
    (⌊3 * (N : ℝ) / regularDecompositionBucketWidth ε N⌋₊ : ℝ) + 1 ≤ 48 / ε + 1 := by
  have hw : (0 : ℝ) < regularDecompositionBucketWidth ε N :=
    Nat.cast_pos.mpr (regularDecomposition_bucketWidth_pos hεN)
  have hround := (regularDecomposition_rounding_bounds hεN).2.2.1
  have hratio : 3 * (N : ℝ) / regularDecompositionBucketWidth ε N ≤ 48 / ε := by
    apply (div_le_iff₀ hw).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hfloor := (Nat.floor_le (by positivity)).trans hratio
  linarith

set_option exponentiation.threshold 512 in
/-- The manuscript's literal `3.33` coefficient bounds `log₂ 10`, checked by the exact
integer inequality `10^100 ≤ 2^333`. -/
theorem log_ten_div_log_two_le : Real.log (10 : ℝ) / Real.log 2 ≤ 333 / 100 := by
  have hpow : (10 : ℝ) ^ (100 : ℕ) ≤ (2 : ℝ) ^ (333 : ℕ) := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 10 ^ (100 : ℕ)) hpow
  rw [Real.log_pow, Real.log_pow] at h
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  norm_num at h
  linarith

/-- The exact rounded type count fits the manuscript's (P2) budget. -/
theorem regularDecomposition_typeCount_budget {ε κ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    {N : ℕ} (hεN : 16 ≤ ε * N)
    (hbudget : Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤ κ * N / 4) :
    (((⌊3 * (N : ℝ) / regularDecompositionBucketWidth ε N⌋₊ + 1) *
      10 ^ regularDecompositionBlockCount ε N : ℕ) : ℝ) ≤ (2 : ℝ) ^ (κ * N / 4) := by
  let M := ⌊3 * (N : ℝ) / regularDecompositionBucketWidth ε N⌋₊
  let L := regularDecompositionBlockCount ε N
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hMpos : (0 : ℝ) < M + 1 := by positivity
  have hM : (M : ℝ) + 1 ≤ 49 / ε := by
    have hb := regularDecomposition_terminalClassCount_le hε hεN
    have h49 : 48 / ε + 1 ≤ 49 / ε := by
      apply (le_div_iff₀ hε).mpr
      field_simp
      nlinarith
    exact hb.trans h49
  have hL := regularDecomposition_blockCount_le hε hεN
  have hlogM := Real.log_le_log hMpos hM
  have hlogten : Real.log (10 : ℝ) ≤ (333 / 100 : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlogtwo).mp log_ten_div_log_two_le
  have hLlog := (mul_le_mul_of_nonneg_right hL
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10))).trans
      (mul_le_mul_of_nonneg_left hlogten (by positivity : (0 : ℝ) ≤ 8 / ε + 1))
  have hbudget' : Real.log (49 / ε) + (333 / 100 : ℝ) * (8 / ε + 1) * Real.log 2 ≤
      κ * N / 4 * Real.log 2 := by
    have h := (div_le_iff₀ hlogtwo).mp (show Real.log (49 / ε) / Real.log 2 ≤
      κ * N / 4 - (333 / 100 : ℝ) * (8 / ε + 1) by linarith)
    nlinarith
  push_cast
  apply (Real.log_le_log_iff (by positivity)
    (Real.rpow_pos_of_pos (by norm_num) _)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact (add_le_add hlogM hLlog).trans (by nlinarith)

/-- A planar block has at most `2^(8w)` terminal descendant cells at the chosen bucket width. -/
theorem regularDecomposition_childCount_le {ε : ℝ} {N : ℕ} (hεN : 16 ≤ ε * N) :
    4 ^ regularDecompositionBlockLength ε N ≤ 2 ^ (8 * regularDecompositionBucketWidth ε N) := by
  calc
    _ = 2 ^ (2 * regularDecompositionBlockLength ε N) := by rw [pow_mul]; rfl
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (regularDecomposition_branching_exponent_le hεN)

/-- The actual intermediate-depth regularity factor is strictly less than `R^ε`. -/
theorem regularDecomposition_regularity_factor_lt {ε : ℝ} {N : ℕ} (hεN : 16 ≤ ε * N) :
    (2 : ℝ) ^ (2 * regularDecompositionBlockLength ε N + regularDecompositionBucketWidth ε N) <
      (2 : ℝ) ^ (ε * N) := by
  obtain ⟨_, hdhi, _, hwhi⟩ := regularDecomposition_rounding_bounds hεN
  rw [← Real.rpow_natCast]
  apply (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
  push_cast
  linarith

end FalconerThetaGauge
