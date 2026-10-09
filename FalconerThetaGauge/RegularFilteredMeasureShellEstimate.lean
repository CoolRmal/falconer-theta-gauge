/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryShellClosing
public import FalconerThetaGauge.ScheduledStateEnergiesEntry

/-! # The actual global source shell estimate after the remaining space recurrence -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Metric
open scoped Classical

namespace FalconerThetaGauge

/-- All source 9.3 steps are genuine; the remaining input is precisely actual Move 4. -/
theorem regularFilteredDistanceMeasure_shell_bound_of_space_split
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hballμ : HasGaugeBallBound μ θ C) (hballν : HasGaugeBallBound ν θ C)
    {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1)
    (hSball : S ⊆ ball x₀ (1 / 400)) (hTball : T ⊆ ball y₀ (1 / 400))
    (hspaceμ : ∀ t : RegularRetainedType μ θ N,
      ActualSpaceSplittingRecurrence (regularRetainedProbability μ θ N t) θ N)
    (hspaceν : ∀ t : RegularRetainedType ν θ N,
      ActualSpaceSplittingRecurrence (regularRetainedProbability ν θ N t) θ N) :
    scalarFourierAnnulusIntegral
        (regularFilteredDistanceMeasure μ ν hpar (8 * expansionCount θ N))
        ((N : ℝ) - 1) ((N : ℝ) + 1) ≤ (2 : ℝ) ^ (-gain θ N * N / 3) :=
  regularFilteredDistanceMeasure_shell_bound_of_entry_state_bounds μ ν hθ hC hballμ hballν
    hpar hconstant hab hS hT hμ hν hSball hTball
    (fun t ↦ regularRetainedEntryStateEnergy_le_source_of_space_split μ hθ hC hballμ hpar
      hconstant t (hspaceμ t))
    (fun t ↦ regularRetainedEntryStateEnergy_le_source_of_space_split ν hθ hC hballν hpar
      hconstant t (hspaceν t))

end FalconerThetaGauge
