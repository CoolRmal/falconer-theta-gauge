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

open Filter
open scoped Topology

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

theorem gain_mul_scale (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    gain θ N * N = gainCoefficient θ * (N : ℝ) ^ θ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [gain_eq_mul_rpow θ hN, Real.rpow_sub hN' θ 1, Real.rpow_one]
  field_simp

/-- The gain shrinks with terminal scale, so fixed-parameter thresholds do not
directly establish estimates at these parameters. -/
theorem tendsto_gain_zero (θ : ℝ) (hθ : θ < 1) :
    Tendsto (gain θ) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (θ - 1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext N
    congr 1
    ring
  have h := hp.const_mul (gainCoefficient θ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (gain_eq_mul_rpow θ (lt_of_lt_of_le Nat.zero_lt_one hN)).symm

/-- Although the gain shrinks, its scale-multiplied exponent diverges. -/
theorem tendsto_gain_mul_scale_atTop (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun N : ℕ ↦ gain θ N * N) atTop atTop := by
  have h := ((tendsto_rpow_atTop hθ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop (gainCoefficient_pos θ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (gain_mul_scale θ (lt_of_lt_of_le Nat.zero_lt_one hN)).symm

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

/-- Rounding costs at most a factor of two once the unrounded block count is
large. This is the upper block bound in (P4). -/
theorem eventually_blockParameter_le_gain_div (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, blockParameter θ N ≤ gain θ N / 500 := by
  filter_upwards [(tendsto_gain_mul_scale_atTop θ hθ).eventually
    (eventually_ge_atTop 1000), eventually_ge_atTop 1] with N hlarge hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hinv : 1 / (N : ℝ) ≤ gain θ N / 1000 := by
    apply (div_le_iff₀ hNreal).mpr
    nlinarith
  have hround := blockParameter_lt_gain_div_add θ hNpos
  linarith

/-- Every positive integer power of the gain has an exact power-law exponent
after multiplying by the terminal scale. -/
theorem gain_pow_mul_scale (θ : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    gain θ N ^ k * N = gainCoefficient θ ^ k *
      (N : ℝ) ^ ((θ - 1) * k + 1) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [gain_eq_mul_rpow θ hN, mul_pow,
    Real.rpow_add_one hN'.ne', Real.rpow_mul_natCast hN'.le]
  ring

/-- The rounded block parameter retains a quantitative lower power bound. -/
theorem blockParameter_pow_mul_scale_lower (θ : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (gainCoefficient θ / 1000) ^ k * (N : ℝ) ^ ((θ - 1) * k + 1) ≤
      blockParameter θ N ^ k * N := by
  have hgain : 0 ≤ gain θ N / 1000 := (div_pos (gain_pos θ hN) (by norm_num)).le
  have hp := pow_le_pow_left₀ hgain (gain_div_le_blockParameter θ hN) k
  have h := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [div_pow, div_mul_eq_mul_div, gain_pow_mul_scale θ k hN] at h
  simpa only [div_pow, div_mul_eq_mul_div, mul_div_assoc] using h

/-- Positive exponents in the rounded block power retain divergence. -/
theorem tendsto_blockParameter_pow_mul_scale_atTop (θ : ℝ) (k : ℕ)
    (hexp : 0 < (θ - 1) * k + 1) :
    Tendsto (fun N : ℕ ↦ blockParameter θ N ^ k * N) atTop atTop := by
  have hc : 0 < (gainCoefficient θ / 1000) ^ k := by
    exact pow_pos (div_pos (gainCoefficient_pos θ) (by norm_num)) k
  have hp := ((tendsto_rpow_atTop hexp).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hp
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact blockParameter_pow_mul_scale_lower θ k (lt_of_lt_of_le Nat.zero_lt_one hN)

/-- The exact rounded block parameter absorbs logarithmic branch costs above
the two-thirds threshold: `κ_N³ N` dominates every fixed logarithmic cost. -/
theorem eventually_log_le_blockParameter_cube_mul_scale (θ c : ℝ)
    (hθ : 2 / 3 < θ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ c * blockParameter θ N ^ 3 * N := by
  have ha : 0 < (gainCoefficient θ / 1000) ^ 3 := by
    exact pow_pos (div_pos (gainCoefficient_pos θ) (by norm_num)) 3
  filter_upwards [eventually_branchCost θ (c * (gainCoefficient θ / 1000) ^ 3)
    hθ (mul_pos hc ha), eventually_ge_atTop 1] with N hlog hN
  have hb := blockParameter_pow_mul_scale_lower θ 3 (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hexp : (θ - 1) * (3 : ℝ) + 1 = 3 * θ - 2 := by ring
  norm_num only [Nat.cast_ofNat] at hb
  rw [hexp] at hb
  exact hlog.trans (by nlinarith)

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

/-- The upper tolerance rounding error is one inverse terminal scale. -/
theorem tolerance_lt_blockParameter_sq_div_add (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    tolerance θ N < blockParameter θ N ^ 2 / 1000000 + 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Nat.ceil_lt_add_one (show 0 ≤ blockParameter θ N ^ 2 * N / 1000000 by
    positivity)
  unfold tolerance toleranceCount
  apply (div_lt_iff₀ hN').mpr
  convert h using 1
  field_simp

/-- This is the upper tolerance bound in (P4), with the exact integer ceiling. -/
theorem eventually_tolerance_le_blockParameter_sq_div (θ : ℝ) (hθ : 1 / 2 < θ) :
    ∀ᶠ N : ℕ in atTop, tolerance θ N ≤ blockParameter θ N ^ 2 / 500000 := by
  have hexp : 0 < (θ - 1) * (2 : ℝ) + 1 := by linarith
  have hp := tendsto_blockParameter_pow_mul_scale_atTop θ 2 (by simpa using hexp)
  filter_upwards [hp.eventually (eventually_ge_atTop 1000000),
    eventually_ge_atTop 1] with N hlarge hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hinv : 1 / (N : ℝ) ≤ blockParameter θ N ^ 2 / 1000000 := by
    apply (div_le_iff₀ hNreal).mpr
    nlinarith
  have hround := tolerance_lt_blockParameter_sq_div_add θ hNpos
  linarith

/-- The actual rounded tolerance has the lower growth rate used to sum the
removed masses; its integer rounding is retained. -/
theorem tolerance_mul_scale_lower (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    ((gainCoefficient θ / 1000) ^ 2 / 1000000) * (N : ℝ) ^ (2 * θ - 1) ≤
      tolerance θ N * N := by
  have hb := blockParameter_pow_mul_scale_lower θ 2 hN
  have ht := mul_le_mul_of_nonneg_right (blockParameter_sq_div_le_tolerance θ hN)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hexp : (θ - 1) * (2 : ℝ) + 1 = 2 * θ - 1 := by ring
  norm_num only [Nat.cast_ofNat] at hb
  rw [hexp] at hb
  nlinarith

/-- Unlike its vanishing tolerance, the scale-multiplied tolerance diverges
for every exponent above one half. -/
theorem tendsto_tolerance_mul_scale_atTop (θ : ℝ) (hθ : 1 / 2 < θ) :
    Tendsto (fun N : ℕ ↦ tolerance θ N * N) atTop atTop := by
  have hc : 0 < (gainCoefficient θ / 1000) ^ 2 / 1000000 := by
    have := gainCoefficient_pos θ
    positivity
  have hp := ((tendsto_rpow_atTop (by linarith : 0 < 2 * θ - 1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hp
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact tolerance_mul_scale_lower θ (lt_of_lt_of_le Nat.zero_lt_one hN)

/-- The manuscript's rounded filter error is itself summable, rather than
only its asymptotic model. -/
theorem summable_rounded_filter_error (θ : ℝ) (hθ : 2 / 3 < θ) :
    Summable (fun N : ℕ ↦ (tolerance θ N * N) ^ (-8 : ℝ)) := by
  let c : ℝ := (gainCoefficient θ / 1000) ^ 2 / 1000000
  have hc : 0 < c := by
    have := gainCoefficient_pos θ
    dsimp [c]
    positivity
  apply summable_of_isBigO_nat (summable_filter_power θ hθ)
  apply Asymptotics.IsBigO.of_bound (c ^ (-8 : ℝ))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlower := tolerance_mul_scale_lower θ hNpos
  have hp : 0 < c * (N : ℝ) ^ (2 * θ - 1) := by positivity
  have hbound := Real.rpow_le_rpow_of_nonpos hp hlower (by norm_num : (-8 : ℝ) ≤ 0)
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hNreal.le _),
    ← Real.rpow_mul hNreal.le] at hbound
  have hexp : (2 * θ - 1) * (-8 : ℝ) = -8 * (2 * θ - 1) := by ring
  rw [hexp] at hbound
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg
      (mul_nonneg (tolerance_pos θ hNpos).le hNreal.le) _),
    abs_of_nonneg (Real.rpow_nonneg hNreal.le _)] using hbound

end FalconerThetaGauge
