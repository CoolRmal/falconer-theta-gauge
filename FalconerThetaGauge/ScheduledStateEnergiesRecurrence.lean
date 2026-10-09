module

public import FalconerThetaGauge.ScheduledStateEnergiesLinearization
public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwoEstimate
public import FalconerThetaGauge.ScheduledStateEnergiesMoveThreeEstimate
public import FalconerThetaGauge.RegularMeasureEntryTransitionWeights

/-! # Genuine local recurrences over the literal finite child enumeration -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- The actual child contribution, with Table 1 coefficients and mask-level changes. -/
def regularMeasureChildrenEnergy (ρ : Measure Plane) (θ : ℝ) (N i : ℕ)
    (s : ProfileChainState) : ℝ :=
  ∑ u ∈ profileChildStates (regularMeasureExcess ρ N) (blockCount θ N) N
      (toleranceCount θ N) s,
    profileTransitionMultiplier (regularMeasureExcess ρ N) (blockCount θ N) N
      (tolerance θ N) s u *
      regularMeasureStateEnergy ρ θ N (i + profileTransitionLevelIncrement u) u

theorem regularMeasureChildrenEnergy_nonneg (ρ : Measure Plane) (θ : ℝ) (N i : ℕ)
    (s : ProfileChainState) : 0 ≤ regularMeasureChildrenEnergy ρ θ N i s :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (profileTransitionMultiplier_nonneg ..)
    (regularMeasureStateEnergy_nonneg ..)

theorem regularMeasureChildrenEnergy_right_split (ρ : Measure Plane) (θ : ℝ) (N i a t : ℕ)
    (hlong : 100 * blockCount θ N < t - a)
    (hright : a + t <
      2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) :
    regularMeasureChildrenEnergy ρ θ N i (.discrepancy a t) =
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) t +
          7 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy a
          (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t)) := by
  simp only [regularMeasureChildrenEnergy, profileChildStates, ProfileChainState.finish,
    ProfileChainState.start, hlong, ite_true, profileLongChildStates, hright, sum_singleton,
    profileTransitionMultiplier, profileTransitionLevelIncrement, ProfileChainState.isFourier,
    Bool.false_eq_true, ite_false]

theorem regularMeasureChildrenEnergy_left_split (ρ : Measure Plane) (θ : ℝ) (N i a t : ℕ)
    (hlong : 100 * blockCount θ N < t - a)
    (hleft : 2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t ≤ a + t) :
    regularMeasureChildrenEnergy ρ θ N i (.discrepancy a t) =
      320 * regularMeasureStateEnergy ρ θ N (i + 1)
        (.discrepancy a (t - toleranceCount θ N)) +
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) a
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) +
          13 * tolerance θ N)) *
        ∑ v ∈ Ioc (t - toleranceCount θ N) t,
          regularMeasureStateEnergy ρ θ N i (.fourier a t
            (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) v) := by
  have hright : ¬a + t <
      2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t := by omega
  have hd : Disjoint ({ProfileChainState.discrepancy a (t - toleranceCount θ N)})
      ((Finset.Ioc (t - toleranceCount θ N) t).image fun v ↦ ProfileChainState.fourier a t
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) v) := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_image]
    rintro ⟨v, _, hv⟩
    cases hv
  simp only [regularMeasureChildrenEnergy, profileChildStates, ProfileChainState.finish,
    ProfileChainState.start, hlong, ite_true, profileLongChildStates, hright, ite_false]
  rw [sum_union hd, sum_singleton, sum_image]
  · simp only [profileTransitionMultiplier, hright, ite_false, ProfileChainState.isFourier,
      profileTransitionLevelIncrement, Bool.false_eq_true, ite_true, add_zero, ← mul_sum]
  · intro v _ w _ hvw
    cases hvw
    rfl

/-- Both discrepancy cases now satisfy the actual one-step recurrence. -/
theorem regularMeasureStateEnergy_discrepancy_recurrence (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (a t : ℕ) (ht : t ≤ N)
    (hlong : 100 * blockCount θ N < t - a) :
    regularMeasureStateEnergy ρ θ N i (.discrepancy a t) ≤
      regularMeasureChildrenEnergy ρ θ N i (.discrepancy a t) +
        (2 : ℝ) ^ (-(25 * (N : ℝ))) := by
  by_cases hright : a + t <
      2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t
  · rw [regularMeasureChildrenEnergy_right_split ρ θ N i a t hlong hright]
    exact (regularMeasureStateEnergy_moveOne ρ hρ hpar hreg i hi a t ht hlong hright).trans
      (le_add_of_nonneg_right (by positivity))
  · rw [regularMeasureChildrenEnergy_left_split ρ θ N i a t hlong (by omega)]
    exact regularMeasureStateEnergy_moveTwo ρ hρ hpar hreg i hi a t ht hlong (by omega)

/-- Every tied longest-test child is present with its actual refinement coefficient. -/
theorem regularMeasureStateEnergy_refinement_recurrence (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (b e a v : ℕ)
    (hs : (ProfileChainState.fourier b e a v).Valid N (toleranceCount θ N))
    (hlong : 100 * blockCount θ N < v - a)
    (hlarge : v - a ≤ 2 * profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a) :
    regularMeasureStateEnergy ρ θ N i (.fourier b e a v) ≤
      regularMeasureChildrenEnergy ρ θ N i (.fourier b e a v) +
        (2 : ℝ) ^ (-(25 * (N : ℝ))) := by
  have hL : 0 < profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a := by omega
  obtain ⟨test, htest, hlargest⟩ := profileLongestTestLength_attained hL
  let move : ProfileChainMove (regularMeasureExcess ρ N) (blockCount θ N) N
      (toleranceCount θ N) (.fourier b e a v) (.fourier b e test.anchor v) :=
    .refine b e a v hlong test htest hlargest (by omega)
  have hh := regularMeasureStateEnergy_moveThree_le_uniform_error ρ hρ hpar hreg i hi
    b e a v hs hlong test htest hlargest (by omega)
  have hc : move.upperMultiplier (tolerance θ N) *
      regularMeasureStateEnergy ρ θ N i (.fourier b e test.anchor v) ≤
        regularMeasureChildrenEnergy ρ θ N i (.fourier b e a v) := by
    rw [move.upperMultiplier_eq_transition]
    change profileTransitionMultiplier _ _ _ _ _ _ *
      regularMeasureStateEnergy ρ θ N (i + profileTransitionLevelIncrement
        (.fourier b e test.anchor v)) (.fourier b e test.anchor v) ≤ _
    unfold regularMeasureChildrenEnergy
    apply Finset.single_le_sum
      (f := fun u ↦ profileTransitionMultiplier (regularMeasureExcess ρ N)
        (blockCount θ N) N (tolerance θ N) (.fourier b e a v) u *
        regularMeasureStateEnergy ρ θ N (i + profileTransitionLevelIncrement u) u)
    · intro u _
      exact mul_nonneg (profileTransitionMultiplier_nonneg ..)
        (regularMeasureStateEnergy_nonneg ..)
    · exact move.mem_childStates
  exact hh.trans (add_le_add hc le_rfl)

end FalconerThetaGauge
