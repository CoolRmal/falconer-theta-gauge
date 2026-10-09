module

public import FalconerThetaGauge.ScheduledStateEnergiesRecurrence
public import FalconerThetaGauge.RegularMeasureEntryTreeTelescope

/-! # Actual analytic node values in the multiplicity-preserving induction telescope -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem ProfileMoveChain.children_sum {A : ℕ → ℝ} {q N δ : ℕ}
    (chain : ProfileMoveChain A q N δ) (f : ProfileMoveChain A q N δ → ℝ) :
    (chain.children.val.map f).sum =
      ∑ u ∈ (profileChildStates A q N δ (chain.state chain.length)).attach,
        f (chain.append u.val (Classical.choice (profileChildStates_move u.property))) := by
  change (∑ child ∈ chain.children, f child) = _
  unfold ProfileMoveChain.children
  apply Finset.sum_image
  intro u _ v _ huv
  apply Subtype.ext
  have hh := congrArg (fun child ↦ child.state child.length) huv
  simpa only [ProfileMoveChain.append_state_final] using hh

/-- An actual analytic node value, including its literal full-path coefficient. -/
def actualProfileNodeEnergy (ρ : Measure Plane) (θ : ℝ) (N initial : ℕ)
    (chain : ProfileMoveChain (regularMeasureExcess ρ N)
      (blockCount θ N) N (toleranceCount θ N)) : ℝ :=
  chain.multiplierProduct (tolerance θ N) *
    regularMeasureStateEnergy ρ θ N (chain.maskLevel initial) (chain.state chain.length)

theorem actualProfileNodeEnergy_root (ρ : Measure Plane) (θ : ℝ) (N initial : ℕ)
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N)) :
    actualProfileNodeEnergy ρ θ N initial (ProfileMoveChain.root s hs) =
      regularMeasureStateEnergy ρ θ N initial s := by
  simp only [actualProfileNodeEnergy, ProfileMoveChain.multiplierProduct,
    ProfileMoveChain.maskLevel, ProfileMoveChain.root, range_zero, Finset.prod_empty, sum_empty,
    add_zero, one_mul]

/-- Appending the actual chosen transition yields exactly the corresponding child term. -/
theorem actualProfileNodeEnergy_children (ρ : Measure Plane) (θ : ℝ) (N initial : ℕ)
    (chain : ProfileMoveChain (regularMeasureExcess ρ N)
      (blockCount θ N) N (toleranceCount θ N)) :
    (chain.children.val.map (actualProfileNodeEnergy ρ θ N initial)).sum =
      chain.multiplierProduct (tolerance θ N) *
        regularMeasureChildrenEnergy ρ θ N (chain.maskLevel initial)
          (chain.state chain.length) := by
  rw [ProfileMoveChain.children_sum]
  simp only [actualProfileNodeEnergy, ProfileMoveChain.append_multiplierProduct,
    ProfileMoveChain.append_maskLevel, ProfileMoveChain.append_state_final,
    ProfileChainMove.upperMultiplier_eq_transition, ProfileChainMove.levelIncrement_eq_transition,
    mul_assoc]
  rw [← Finset.mul_sum]
  unfold regularMeasureChildrenEnergy
  congr 1
  exact Finset.sum_attach
    (profileChildStates (regularMeasureExcess ρ N) (blockCount θ N) N
      (toleranceCount θ N) (chain.state chain.length))
    (fun u ↦ profileTransitionMultiplier (regularMeasureExcess ρ N) (blockCount θ N) N
      (tolerance θ N) (chain.state chain.length) u *
      regularMeasureStateEnergy ρ θ N
        (chain.maskLevel initial + profileTransitionLevelIncrement u) u)

/-- The completed local recurrence hypotheses suffice to telescope the genuine analytic tree. -/
theorem regularMeasureStateEnergy_le_actual_tree (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (hrec : ∀ i, i + 1 ≤ maskLevelCount θ N → ∀ s : ProfileChainState,
      s.Valid N (toleranceCount θ N) →
      100 * blockCount θ N < s.finish - s.start →
      regularMeasureStateEnergy ρ θ N i s ≤ regularMeasureChildrenEnergy ρ θ N i s +
        (2 : ℝ) ^ (-(25 * (N : ℝ))))
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N))
    {initial : ℕ} (hinitial : initial ≤ 1) :
    regularMeasureStateEnergy ρ θ N initial s ≤
      actualProfileTreeTerminalEnergy ρ θ N s hs initial + actualProfileTreeError ρ θ N s hs := by
  have hN : 0 < N := by have := hpar.1; omega
  have hq := blockCount_pos θ hN
  have hδq := toleranceCount_le_blockCount_of_parameterFacts hpar
  have ht := profileInductionVisits_telescope hpar hs (actualProfileNodeEnergy ρ θ N initial)
    (fun chain ↦ chain.multiplierProduct (tolerance θ N) * (2 : ℝ) ^ (-(25 * (N : ℝ))))
    (fun chain _ ↦ mul_nonneg (chain.multiplierProduct_nonneg _) (by positivity)) (by
      intro chain _ hlong
      have hlevel := chain.maskLevel_le_maskLevelCount_sub_two hpar hinitial
      have hv := chain.state_valid hq hδq (le_refl chain.length)
      have hh := hrec (chain.maskLevel initial) (by
        have : 2 ≤ maskLevelCount θ N := by unfold maskLevelCount; omega
        omega) (chain.state chain.length) hv hlong
      rw [actualProfileNodeEnergy_children]
      unfold actualProfileNodeEnergy
      exact (mul_le_mul_of_nonneg_left hh (chain.multiplierProduct_nonneg _)).trans_eq
        (mul_add _ _ _))
  rw [actualProfileNodeEnergy_root] at ht
  unfold actualProfileNodeEnergy at ht
  simpa only [actualProfileTreeTerminalEnergy, actualProfileTreeError, neg_mul] using ht

/-- After true local recurrences, the already proved terminal and error budgets close the tree. -/
theorem regularMeasureStateEnergy_le_tree_budget (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (hrec : ∀ i, i + 1 ≤ maskLevelCount θ N → ∀ s : ProfileChainState,
      s.Valid N (toleranceCount θ N) →
      100 * blockCount θ N < s.finish - s.start →
      regularMeasureStateEnergy ρ θ N i s ≤ regularMeasureChildrenEnergy ρ θ N i s +
        (2 : ℝ) ^ (-(25 * (N : ℝ))))
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ s.finish - s.start)
    {initial : ℕ} (hinitial : initial ≤ 1) :
    regularMeasureStateEnergy ρ θ N initial s ≤
      (2 : ℝ) ^ (N * (-profileBudget (regularMeasureExcess ρ N)
        (blockCount θ N) s.start s.finish + 227 * blockParameter θ N)) := by
  exact (regularMeasureStateEnergy_le_actual_tree ρ hpar hrec s hs hinitial).trans
    (actualProfileTreeTerminalEnergy_add_error_le_budget ρ hρ hpar s hs hroot initial)

end FalconerThetaGauge
