module

public import FalconerThetaGauge.ScheduledStateEnergiesTelescope

/-! # Exact near and far child terms at the remaining space-splitting step -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem regularMeasureChildrenEnergy_space_split (ρ : Measure Plane) (θ : ℝ)
    (N i b e a v : ℕ) (hlong : 100 * blockCount θ N < v - a)
    (hsmall : 2 * profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a < v - a) :
    regularMeasureChildrenEnergy ρ θ N i (.fourier b e a v) =
      81 ^ 2 * regularMeasureStateEnergy ρ θ N i (.fourier b e
        (profileNearStart (regularMeasureExcess ρ N) (blockCount θ N) N
          (toleranceCount θ N) b e a v) v) +
      (2 : ℝ) ^ (90 : ℝ) *
        ∑ n ∈ Finset.Ioo a (min (v + 1)
          (profileNearStart (regularMeasureExcess ρ N) (blockCount θ N) N
            (toleranceCount θ N) b e a v + 12)),
          regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy n v) := by
  let h := profileNearStart (regularMeasureExcess ρ N) (blockCount θ N) N
    (toleranceCount θ N) b e a v
  have hlarge : ¬v - a ≤ 2 * profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a := by omega
  have hd : Disjoint ({ProfileChainState.fourier b e h v})
      ((Finset.Ioo a (min (v + 1) (h + 12))).image fun n ↦
        ProfileChainState.discrepancy n v) := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_image]
    rintro ⟨n, _, hn⟩
    cases hn
  simp only [regularMeasureChildrenEnergy, profileChildStates, ProfileChainState.finish,
    ProfileChainState.start, hlong, ite_true, profileLongChildStates, hlarge, ite_false]
  rw [sum_union hd, sum_singleton, sum_image]
  · simp only [profileTransitionMultiplier, hlarge, ite_false, ProfileChainState.isFourier,
      profileTransitionLevelIncrement, Bool.false_eq_true, ite_true, add_zero, ← mul_sum]
    rfl
  · intro n _ m _ hnm
    cases hnm
    rfl

/-- Full Estimate 7.8 is the sole local analytic input still needed by the tree assembly. -/
def ActualSpaceSplittingRecurrence (ρ : Measure Plane) (θ : ℝ) (N : ℕ) : Prop :=
  ∀ i, i + 1 ≤ maskLevelCount θ N → ∀ b e a v,
    (ProfileChainState.fourier b e a v).Valid N (toleranceCount θ N) →
    100 * blockCount θ N < v - a →
    2 * profileLongestTestLength (regularMeasureExcess ρ N) (blockCount θ N) N b e a < v - a →
    regularMeasureStateEnergy ρ θ N i (.fourier b e a v) ≤
      81 ^ 2 * regularMeasureStateEnergy ρ θ N i (.fourier b e
        (profileNearStart (regularMeasureExcess ρ N) (blockCount θ N) N
          (toleranceCount θ N) b e a v) v) +
      (2 : ℝ) ^ (90 : ℝ) *
        ∑ n ∈ Finset.Ioo a (min (v + 1)
          (profileNearStart (regularMeasureExcess ρ N) (blockCount θ N) N
            (toleranceCount θ N) b e a v + 12)),
          regularMeasureStateEnergy ρ θ N (i + 1) (.discrepancy n v) +
      (2 : ℝ) ^ (-(25 * (N : ℝ)))

/-- The three completed moves and the final actual space split assemble every local recurrence. -/
theorem regularMeasureStateEnergy_recurrence_of_space_split (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hspace : ActualSpaceSplittingRecurrence ρ θ N)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (s : ProfileChainState)
    (hs : s.Valid N (toleranceCount θ N))
    (hlong : 100 * blockCount θ N < s.finish - s.start) :
    regularMeasureStateEnergy ρ θ N i s ≤ regularMeasureChildrenEnergy ρ θ N i s +
      (2 : ℝ) ^ (-(25 * (N : ℝ))) := by
  cases s with
  | discrepancy a t =>
    exact regularMeasureStateEnergy_discrepancy_recurrence ρ hρ hpar hreg i hi a t hs.2 hlong
  | fourier b e a v =>
    by_cases hlarge : v - a ≤ 2 * profileLongestTestLength (regularMeasureExcess ρ N)
        (blockCount θ N) N b e a
    · exact regularMeasureStateEnergy_refinement_recurrence ρ hρ hpar hreg i hi
        b e a v hs hlong hlarge
    · rw [regularMeasureChildrenEnergy_space_split ρ θ N i b e a v hlong (by omega)]
      exact hspace i hi b e a v hs hlong (by omega)

/-- The actual induction is reduced to proving the outstanding source space-splitting estimate. -/
theorem regularMeasureStateEnergy_tree_budget_of_space_split (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hspace : ActualSpaceSplittingRecurrence ρ θ N)
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ s.finish - s.start)
    {initial : ℕ} (hinitial : initial ≤ 1) :
    regularMeasureStateEnergy ρ θ N initial s ≤
      (2 : ℝ) ^ (N * (-profileBudget (regularMeasureExcess ρ N)
        (blockCount θ N) s.start s.finish + 227 * blockParameter θ N)) :=
  regularMeasureStateEnergy_le_tree_budget ρ hρ hpar
    (regularMeasureStateEnergy_recurrence_of_space_split ρ hρ hpar hreg hspace)
    s hs hroot hinitial

end FalconerThetaGauge
