module

public import FalconerThetaGauge.Asymptotics
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The exact parameters of Definition 2.1

These definitions retain the integer roundings in the source. Positivity and
the elementary rounding bounds are proved for positive terminal scale.
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

/-- The manuscript's excess profile `g(n)`. -/
def gaugeExcess (θ : ℝ) (N : ℕ) (n : ℝ) : ℝ :=
  (n * Real.log 2) ^ θ / ((N : ℝ) * Real.log 2)

/-- The gain parameter `β_N = g(N/4)/2`. -/
def gain (θ : ℝ) (N : ℕ) : ℝ := gaugeExcess θ N ((N : ℝ) / 4) / 2

/-- The exact coefficient in `β_N = c_θ N^(θ-1)`. -/
def gainCoefficient (θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.log 2) ^ (θ - 1) * (4 : ℝ) ^ (-θ)

theorem gainCoefficient_pos (θ : ℝ) : 0 < gainCoefficient θ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gainCoefficient
  positivity

theorem gain_eq_mul_rpow (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    gain θ N = gainCoefficient θ * (N : ℝ) ^ (θ - 1) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfour : (4 : ℝ) ^ θ ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) θ).ne'
  unfold gain gaugeExcess gainCoefficient
  rw [Real.mul_rpow (div_nonneg hN'.le (by norm_num)) hlog.le,
    Real.div_rpow hN'.le (by norm_num) θ,
    Real.rpow_sub hlog θ 1, Real.rpow_sub hN' θ 1,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) θ, Real.rpow_one, Real.rpow_one]
  field_simp

/-- The integer block length `q = ⌈βN/1000⌉`. -/
def blockCount (θ : ℝ) (N : ℕ) : ℕ := ⌈gain θ N * (N : ℝ) / 1000⌉₊

/-- The rounded block parameter `κ = q/N`. -/
def blockParameter (θ : ℝ) (N : ℕ) : ℝ := (blockCount θ N : ℝ) / N

/-- The integer tolerance numerator `⌈κ²N/10⁶⌉`. -/
def toleranceCount (θ : ℝ) (N : ℕ) : ℕ :=
  ⌈(blockParameter θ N) ^ 2 * (N : ℝ) / 1000000⌉₊

/-- The rounded regularity tolerance `ε`. -/
def tolerance (θ : ℝ) (N : ℕ) : ℝ := (toleranceCount θ N : ℝ) / N

/-- The number of expansion terms and integrations by parts. -/
def expansionCount (θ : ℝ) (N : ℕ) : ℕ := ⌈240 / tolerance θ N⌉₊

/-- The number of mask levels. -/
def maskLevelCount (θ : ℝ) (N : ℕ) : ℕ :=
  ⌈7 / blockParameter θ N + 1 / tolerance θ N⌉₊ + 3

theorem gain_pos (θ : ℝ) {N : ℕ} (hN : 0 < N) : 0 < gain θ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos (div_pos (Real.rpow_pos_of_pos (by positivity) θ) (mul_pos hN' hlog))
    (by norm_num)

theorem blockCount_pos (θ : ℝ) {N : ℕ} (hN : 0 < N) : 0 < blockCount θ N := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (gain_pos θ hN) (by exact_mod_cast hN)) (by norm_num)

theorem blockParameter_pos (θ : ℝ) {N : ℕ} (hN : 0 < N) : 0 < blockParameter θ N := by
  exact div_pos (by exact_mod_cast blockCount_pos θ hN) (by exact_mod_cast hN)

theorem blockParameter_mul_scale (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    blockParameter θ N * N = (blockCount θ N : ℝ) := by
  exact div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt hN)

theorem gain_div_le_blockParameter (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    gain θ N / 1000 ≤ blockParameter θ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hN').mpr
  have h := Nat.le_ceil (gain θ N * (N : ℝ) / 1000)
  dsimp [blockCount] at *
  nlinarith

theorem blockParameter_lt_gain_div_add (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    blockParameter θ N < gain θ N / 1000 + 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Nat.ceil_lt_add_one (show 0 ≤ gain θ N * (N : ℝ) / 1000 by
    have := gain_pos θ hN
    positivity)
  unfold blockParameter blockCount
  apply (div_lt_iff₀ hN').mpr
  convert h using 1
  field_simp

theorem tolerance_pos (θ : ℝ) {N : ℕ} (hN : 0 < N) : 0 < tolerance θ N := by
  have hk := blockParameter_pos θ hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < toleranceCount θ N := Nat.ceil_pos.mpr (by positivity)
  exact div_pos (by exact_mod_cast hc) hN'

theorem tolerance_mul_scale (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    tolerance θ N * N = (toleranceCount θ N : ℝ) := by
  exact div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt hN)

theorem blockParameter_sq_div_le_tolerance (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    (blockParameter θ N) ^ 2 / 1000000 ≤ tolerance θ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hN').mpr
  have h := Nat.le_ceil ((blockParameter θ N) ^ 2 * (N : ℝ) / 1000000)
  dsimp [toleranceCount] at *
  nlinarith

end FalconerThetaGauge
