/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryTree

/-!
# Actual mask levels along the finite induction

Linearization, low-frequency children, and far children increase the mask
level by one. The other children retain their parent's level. The derived
chain bound places every actual node within the manuscript's mask budget.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The genuine level change in Table 1 for a particular transition. -/
def ProfileChainMove.levelIncrement {A : ℕ → ℝ} {q N δ : ℕ} {s u : ProfileChainState} :
    ProfileChainMove A q N δ s u → ℕ
  | .linearize .. => 1
  | .lowFrequency .. => 1
  | .highFrequency .. => 0
  | .refine .. => 0
  | .near .. => 0
  | .far .. => 1

theorem ProfileChainMove.levelIncrement_le_one {A : ℕ → ℝ} {q N δ : ℕ}
    {s u : ProfileChainState} (move : ProfileChainMove A q N δ s u) :
    move.levelIncrement ≤ 1 := by
  cases move <;> simp [ProfileChainMove.levelIncrement]

namespace ProfileMoveChain

variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)

/-- The actual level increment at a chain index. -/
def levelIncrement (i : ℕ) : ℕ :=
  if hi : i < chain.length then (chain.step i hi).levelIncrement else 0

/-- The actual mask level reached after this chain from a chosen initial level. -/
def maskLevel (initial : ℕ) : ℕ := initial + ∑ i ∈ range chain.length, chain.levelIncrement i

theorem levelIncrement_le_one (i : ℕ) : chain.levelIncrement i ≤ 1 := by
  by_cases hi : i < chain.length
  · simp only [levelIncrement, hi, dite_eq_left]
    exact (chain.step i hi).levelIncrement_le_one
  · simp [levelIncrement, hi]

/-- The actual mask level never exceeds the initial level plus the number of moves. -/
theorem maskLevel_le_length_add_initial (initial : ℕ) :
    chain.maskLevel initial ≤ chain.length + initial := by
  have hsum := Finset.sum_le_sum (s := range chain.length)
    (fun i _ ↦ chain.levelIncrement_le_one i)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hsum
  unfold maskLevel
  omega

/-- Every concrete chain starting at level zero or one remains within `I*−2`. -/
theorem maskLevel_le_maskLevelCount_sub_two {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N))
    {initial : ℕ} (hinitial : initial ≤ 1) :
    chain.maskLevel initial ≤ maskLevelCount θ N - 2 := by
  have hlength := chain.length_le_seven_inverse_block_add_inverse_tolerance hpar
  have hceil : chain.length ≤ ⌈7 / blockParameter θ N + 1 / tolerance θ N⌉₊ := by
    have hreal := hlength.trans (Nat.le_ceil (7 / blockParameter θ N + 1 / tolerance θ N))
    exact_mod_cast hreal
  have hlevel := chain.maskLevel_le_length_add_initial initial
  unfold maskLevelCount
  omega

/-- The actual levels also stay within the finite stationary-expansion order budget. -/
theorem maskLevel_le_expansionCount_sub_two {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N))
    {initial : ℕ} (hinitial : initial ≤ 1) :
    chain.maskLevel initial ≤ expansionCount θ N - 2 :=
  (chain.maskLevel_le_maskLevelCount_sub_two hpar hinitial).trans
    (Nat.sub_le_sub_right hpar.2.2.2.2.2.2.2.2.2.2.1 2)

end ProfileMoveChain

end FalconerThetaGauge
