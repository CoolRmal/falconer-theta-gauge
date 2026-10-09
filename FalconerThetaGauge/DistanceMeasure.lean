module

public import FalconerThetaGauge.Statement
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The positive-length conclusion from a distance measure

The actual pushforward of two planar probabilities by Euclidean distance has
mass one on the all-pairs distance set when both sources are carried by `E`.
Its absolute continuity is therefore sufficient for the conclusion in Theorem 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- The pushforward of the product measure by Euclidean distance. -/
def crossDistanceMeasure (μ ν : Measure Plane) : Measure ℝ :=
  (μ.prod ν).map (fun p : Plane × Plane ↦ dist p.1 p.2)

instance (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (crossDistanceMeasure μ ν) := by
  unfold crossDistanceMeasure
  infer_instance

/-- The product probabilities put all their distance mass on the exact target image. -/
theorem crossDistanceMeasure_distanceSet_eq_one
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Plane} (hE : IsCompact E) (hμ : μ E = 1) (hν : ν E = 1) :
    crossDistanceMeasure μ ν (distanceSet E) = 1 := by
  apply le_antisymm ((measure_mono (subset_univ _)).trans_eq measure_univ)
  unfold crossDistanceMeasure
  rw [Measure.map_apply continuous_dist.measurable (measurableSet_distanceSet hE)]
  have hprod : μ.prod ν (E ×ˢ E) = 1 := by rw [Measure.prod_prod, hμ, hν, one_mul]
  rw [← hprod]
  apply measure_mono
  intro p hp
  exact ⟨p, hp, rfl⟩

/-- Absolute continuity of the actual distance measure proves positive length. -/
theorem volume_distanceSet_pos_of_crossDistanceMeasure_absolutelyContinuous
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Plane} (hE : IsCompact E) (hμ : μ E = 1) (hν : ν E = 1)
    (hAC : crossDistanceMeasure μ ν ≪ volume) : 0 < volume (distanceSet E) := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hnull := hAC hzero
  rw [crossDistanceMeasure_distanceSet_eq_one μ ν hE hμ hν] at hnull
  exact one_ne_zero hnull

end FalconerThetaGauge
