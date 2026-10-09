/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainCount

/-!
# Exact short-chain bounds at the manuscript's parameters

For the actual six transition types, ordinary moves number at most `7 / κ`
and low-frequency children at most `1 / ε`. These are conclusions of the
concrete scheduled-test chain, rather than hypotheses about its counts.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

namespace ProfileMoveChain

/-- The exact count of low-frequency children at the literal rounded parameters. -/
theorem lowFrequency_card_le_inverse_tolerance {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :
    ((chain.movesOfTag 1).card : ℝ) ≤ 1 / tolerance θ N := by
  have hN : 0 < N := by have := hpar.1; omega
  have hε := tolerance_pos θ hN
  have hdrop := chain.lowFrequency_card_mul_thickness_le (blockCount_pos θ hN)
    (toleranceCount_le_blockCount_of_parameterFacts hpar)
  have hdrop' : ((chain.movesOfTag 1).card : ℝ) * (toleranceCount θ N : ℝ) ≤ N :=
    by exact_mod_cast hdrop
  have hscale := tolerance_mul_scale θ hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hε).mpr
  nlinarith

/-- The exact count of linearization children at the literal rounded parameters. -/
theorem linearize_card_le_inverse_block {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :
    ((chain.movesOfTag 0).card : ℝ) ≤ 1 / blockParameter θ N := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have hdrop := chain.linearize_card_mul_block_le (blockCount_pos θ hN)
    (toleranceCount_le_blockCount_of_parameterFacts hpar)
  have hdrop' : ((chain.movesOfTag 0).card : ℝ) * (blockCount θ N : ℝ) ≤ N :=
    by exact_mod_cast hdrop
  have hscale := blockParameter_mul_scale θ hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hκ).mpr
  nlinarith

/-- Lemma 8.7: every actual chain has at most `7 / κ` ordinary moves. -/
theorem ordinary_card_le_seven_inverse_block {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :
    (chain.ordinaryMoves.card : ℝ) ≤ 7 / blockParameter θ N := by
  rcases hpar with ⟨hN₄, hP1, hP2, hP3, hκlo, hκhi, hβhi, hεlo, hεhi, hsmall,
    hlevels, htests⟩
  have hN : 0 < N := by omega
  have hκ := blockParameter_pos θ hN
  have hκupper : blockParameter θ N ≤ 1 / 5 := by linarith
  have hpar' : ParameterFacts θ N :=
    ⟨hN₄, hP1, hP2, hP3, hκlo, hκhi, hβhi, hεlo, hεhi, hsmall, hlevels, htests⟩
  have hcount := chain.ordinary_card_le (blockCount_pos θ hN)
    (toleranceCount_le_blockCount_of_parameterFacts hpar')
  have hcount' : (chain.ordinaryMoves.card : ℝ) ≤ ((chain.movesOfTag 0).card : ℝ) +
      4 * ((profileMarkedDepths A (blockCount θ N) N).card : ℝ) + 2 :=
    by exact_mod_cast hcount
  have hlinear := chain.linearize_card_le_inverse_block hpar'
  have hmarks := profileMarkedDepths_card_le_inverse_block A θ hN
  have hconstant : (10 : ℝ) ≤ 2 / blockParameter θ N := by
    apply (le_div_iff₀ hκ).mpr
    linarith
  have hsum : 1 / blockParameter θ N + 4 * (1 / blockParameter θ N + 2) + 2 ≤
      7 / blockParameter θ N := by
    simp only [div_eq_mul_inv, one_mul] at hconstant ⊢
    linarith
  exact hcount'.trans ((by linarith : ((chain.movesOfTag 0).card : ℝ) +
    4 * ((profileMarkedDepths A (blockCount θ N) N).card : ℝ) + 2 ≤
      1 / blockParameter θ N + 4 * (1 / blockParameter θ N + 2) + 2).trans hsum)

/-- The full finite depth of every actual chain is bounded by the two counts of Lemma 8.7. -/
theorem length_le_seven_inverse_block_add_inverse_tolerance {θ : ℝ} {N : ℕ}
    {A : ℕ → ℝ} (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :
    (chain.length : ℝ) ≤ 7 / blockParameter θ N + 1 / tolerance θ N := by
  have hpartition := Finset.card_filter_add_card_filter_not (s := range chain.length)
    (p := fun i ↦ chain.tag i = 1)
  have heq : (chain.movesOfTag 1).card + chain.ordinaryMoves.card = chain.length := by
    simpa only [movesOfTag, ordinaryMoves, Finset.card_range] using hpartition
  have hordinary := chain.ordinary_card_le_seven_inverse_block hpar
  have hlow := chain.lowFrequency_card_le_inverse_tolerance hpar
  have heq' : ((chain.movesOfTag 1).card : ℝ) + (chain.ordinaryMoves.card : ℝ) =
      chain.length := by exact_mod_cast heq
  linarith

end ProfileMoveChain

end FalconerThetaGauge
