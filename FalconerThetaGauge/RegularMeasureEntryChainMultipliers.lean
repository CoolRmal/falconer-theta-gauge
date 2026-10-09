/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainNumbers

/-!
# Actual finite products of Table 1 multipliers

The upper multipliers retain the literal `7ε`, `13ε`, `12ε`, `320`, `81²`,
and the proven bound `2^90` for the far multiplier. Their product costs at
most the actual accumulated height plus `2κ` on every concrete finite chain.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The exact multipliers of Table 1, with its established far-constant upper bound. -/
def ProfileChainMove.upperMultiplier {A : ℕ → ℝ} {q N δ : ℕ} {s u : ProfileChainState}
    (ε : ℝ) (move : ProfileChainMove A q N δ s u) : ℝ :=
  match move with
  | .linearize .. => (2 : ℝ) ^ ((N : ℝ) * (move.budgetCost + 7 * ε))
  | .lowFrequency .. => 320
  | .highFrequency .. => (2 : ℝ) ^ ((N : ℝ) * (move.budgetCost + 13 * ε))
  | .refine .. => (2 : ℝ) ^ ((N : ℝ) * (move.budgetCost + 12 * ε))
  | .near .. => 81 ^ 2
  | .far .. => (2 : ℝ) ^ (90 : ℝ)

theorem ProfileChainMove.upperMultiplier_nonneg {A : ℕ → ℝ} {q N δ : ℕ}
    {s u : ProfileChainState} (ε : ℝ) (move : ProfileChainMove A q N δ s u) :
    0 ≤ move.upperMultiplier ε := by
  cases move <;> simp only [ProfileChainMove.upperMultiplier] <;> positivity

/-- Each actual ordinary multiplier is charged to its cost and the `13ε` overhead. -/
theorem ProfileChainMove.upperMultiplier_le {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s u : ProfileChainState}
    (move : ProfileChainMove A (blockCount θ N) N (toleranceCount θ N) s u) :
    move.upperMultiplier (tolerance θ N) ≤ (2 : ℝ) ^ ((N : ℝ) * move.budgetCost) *
      (if move.tag = 1 then 320 else (2 : ℝ) ^ (13 * tolerance θ N * N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hε := tolerance_pos θ hN
  have hnearfar := parameter_near_far_constant_bound hpar
  cases move with
  | linearize a t hlong hright =>
    norm_num only [ProfileChainMove.upperMultiplier, ProfileChainMove.tag]
    simp only [ite_false]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  | lowFrequency a t hlong hleft =>
    simp [ProfileChainMove.upperMultiplier, ProfileChainMove.budgetCost, ProfileChainMove.tag]
  | highFrequency a t v hlong hleft hvlo hvhi =>
    norm_num only [ProfileChainMove.upperMultiplier, ProfileChainMove.tag]
    simp only [ite_false]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply le_of_eq
    congr 1
    ring
  | refine b e a v hlong test htest hlargest hlarge =>
    norm_num only [ProfileChainMove.upperMultiplier, ProfileChainMove.tag]
    simp only [ite_false]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  | near b e a v hlong hsmall =>
    simpa [ProfileChainMove.upperMultiplier, ProfileChainMove.budgetCost,
      ProfileChainMove.tag] using hnearfar.1
  | far b e a v n hlong hsmall hnlo hnhi hnv =>
    simpa [ProfileChainMove.upperMultiplier, ProfileChainMove.budgetCost,
      ProfileChainMove.tag] using hnearfar.2

namespace ProfileMoveChain

variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)

/-- The actual Table 1 upper multiplier at a finite-chain index. -/
def multiplier (ε : ℝ) (i : ℕ) : ℝ :=
  if hi : i < chain.length then (chain.step i hi).upperMultiplier ε else 1

/-- The actual finite product of the Table 1 upper multipliers. -/
def multiplierProduct (ε : ℝ) : ℝ := ∏ i ∈ range chain.length, chain.multiplier ε i

theorem multiplier_eq (ε : ℝ) {i : ℕ} (hi : i < chain.length) :
    chain.multiplier ε i = (chain.step i hi).upperMultiplier ε := by
  simp only [multiplier, hi, dite_eq_left]

/-- The exact finite product is bounded using its actual ordinary and low-frequency counts. -/
theorem multiplierProduct_le_count_expression {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :
    chain.multiplierProduct (tolerance θ N) ≤ (2 : ℝ) ^ ((N : ℝ) * chain.totalCost) *
      (320 : ℝ) ^ (chain.movesOfTag 1).card *
        ((2 : ℝ) ^ (13 * tolerance θ N * N)) ^ chain.ordinaryMoves.card := by
  unfold multiplierProduct
  calc
    _ ≤ ∏ i ∈ range chain.length, (2 : ℝ) ^ ((N : ℝ) * chain.cost i) *
        (if chain.tag i = 1 then 320 else (2 : ℝ) ^ (13 * tolerance θ N * N)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        rw [chain.multiplier_eq _ (Finset.mem_range.mp hi)]
        exact (chain.step i (Finset.mem_range.mp hi)).upperMultiplier_nonneg _
      · intro i hi
        rw [chain.multiplier_eq _ (Finset.mem_range.mp hi),
          chain.cost_eq (Finset.mem_range.mp hi), chain.tag_eq (Finset.mem_range.mp hi)]
        exact (chain.step i (Finset.mem_range.mp hi)).upperMultiplier_le hpar
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2),
        ← Finset.mul_sum, Finset.prod_ite]
      simp only [Finset.prod_const, totalCost, movesOfTag, ordinaryMoves, mul_assoc]

/-- The actual finite product pays exactly its total cost plus at most `2κ`. -/
theorem multiplierProduct_le_totalCost_add_two_block {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :
    chain.multiplierProduct (tolerance θ N) ≤
      (2 : ℝ) ^ ((N : ℝ) * (chain.totalCost + 2 * blockParameter θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hκ := blockParameter_pos θ hN
  have hε := tolerance_pos θ hN
  have hlowcount := chain.lowFrequency_card_le_inverse_tolerance hpar
  have hordinarycount := chain.ordinary_card_le_seven_inverse_block hpar
  have hordinaryloss := parameter_ordinary_multiplier_loss hpar
  have hlow : (320 : ℝ) ^ (chain.movesOfTag 1).card ≤
      (2 : ℝ) ^ (blockParameter θ N * N) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hlowcount).trans
      (parameter_lowFrequency_constant_bound hpar)
  have hordinary : ((2 : ℝ) ^ (13 * tolerance θ N * N)) ^ chain.ordinaryMoves.card ≤
      (2 : ℝ) ^ (blockParameter θ N * N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc
      _ = (N : ℝ) * (13 * tolerance θ N * (chain.ordinaryMoves.card : ℝ)) := by ring
      _ ≤ (N : ℝ) * (13 * tolerance θ N * (7 / blockParameter θ N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hordinarycount (by positivity)) hN'
      _ ≤ (N : ℝ) * blockParameter θ N := mul_le_mul_of_nonneg_left hordinaryloss hN'
      _ = _ := by ring
  calc
    _ ≤ (2 : ℝ) ^ ((N : ℝ) * chain.totalCost) * (320 : ℝ) ^ (chain.movesOfTag 1).card *
        ((2 : ℝ) ^ (13 * tolerance θ N * N)) ^ chain.ordinaryMoves.card :=
      chain.multiplierProduct_le_count_expression hpar
    _ ≤ (2 : ℝ) ^ ((N : ℝ) * chain.totalCost) * (2 : ℝ) ^ (blockParameter θ N * N) *
        (2 : ℝ) ^ (blockParameter θ N * N) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (by norm_num) _))
        hordinary (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end ProfileMoveChain

end FalconerThetaGauge
