/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureReconstructionThreshold
public import FalconerThetaGauge.ScheduledStateEnergiesSpaceActual

/-! # Absolute continuity for the actual prepared weighted distance measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- True filtering, all four true state moves, and true Fourier reconstruction close the proof. -/
theorem weightedCrossDistanceMeasure_absolutelyContinuous
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ C K : ℝ} (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) (hC : 0 < C) (hK : 0 ≤ K)
    (hballμ : HasGaugeBallBound μ θ C) (hballν : HasGaugeBallBound ν θ C)
    (hunitμ : μ unitSquare = 1) (hunitν : ν unitSquare = 1)
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1)
    (hSball : S ⊆ ball x₀ (1 / 400)) (hTball : T ⊆ ball y₀ (1 / 400))
    (hpinμ : ∀ x ∈ S,
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      radialOrliczMoment ν 8 x ≤ ENNReal.ofReal K)
    (hpinν : ∀ y ∈ T,
      circleArcLength.withDensity (radialProjectionDensity μ y) = μ.map (radialProjection y) ∧
      radialOrliczMoment μ 8 y ≤ ENNReal.ofReal K) :
    weightedCrossDistanceMeasure μ ν ≪ volume := by
  apply weightedCrossDistanceMeasure_absolutelyContinuous_of_space_split_all_scales
    μ ν hθ₀ hθ₁ hC hK hballμ hballν hunitμ hunitν hab hS hT hμ hν hSball hTball
    hpinμ hpinν
  · intro N hpar t
    have hp := regularDyadicPartMeasure_probability μ (tolerance θ N) (blockParameter θ N)
      N t.property
    let : IsProbabilityMeasure (regularRetainedProbability μ θ N t) := hp.1
    exact actualSpaceSplittingRecurrence (regularRetainedProbability μ θ N t) hp.2 hpar
  · intro N hpar t
    have hp := regularDyadicPartMeasure_probability ν (tolerance θ N) (blockParameter θ N)
      N t.property
    let : IsProbabilityMeasure (regularRetainedProbability ν θ N t) := hp.1
    exact actualSpaceSplittingRecurrence (regularRetainedProbability ν θ N t) hp.2 hpar

end FalconerThetaGauge
