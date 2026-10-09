module

public import FalconerThetaGauge.Statement
public import FalconerThetaGauge.RadialProjectionSpread
public import FalconerThetaGauge.FilteredDistanceMeasureGeometry
public import FalconerThetaGauge.DistanceScaling

/-!
# Theorem 1.1: proof target

The exact manuscript statement is recorded here. The proved preparation and
weighted distance carrier reduce the remaining proof to absolute continuity
of the actual weighted distance measure. The comparator must reject this
module while that analytic step depends on `sorryAx`.
-/

@[expose] public section

open MeasureTheory Set

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- Theorem 1.1 of the source PDF, with its exact parameter interval,
compactness hypothesis, arbitrary-gauge Hausdorff measure, and unpinned conclusion. -/
theorem theorem_one_one (θ : ℝ) (E : Set Plane)
    (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) : 0 < volume (distanceSet E) := by
  obtain ⟨ℓ, _C, _K, z, _a, _b, S₁, S₂, μ₁, μ₂, hℓ, _hC, _hK, hS₁, hS₂,
    hsub₁, hsub₂, hmass₁, hmass₂, _hsupp₁, _hsupp₂, _hab, _hball₁, _hball₂,
    _hsq₁, _hsq₂, hsep, _hgb₁, _hgb₂, _henergy, _hpin₁, _hpin₂⟩ :=
    exists_prepared_probabilityMeasures_uniform_radial_orlicz (by linarith) hθ₁.le hE hGauge
  have hcopy : IsCompact (affineMap ℓ z '' E) :=
    hE.image (continuous_affineMap ℓ z)
  have hμ₁copy : (μ₁ : Measure Plane) (affineMap ℓ z '' E) = 1 :=
    le_antisymm (by
      have h : (μ₁ : Measure Plane) (affineMap ℓ z '' E) ≤ (μ₁ : Measure Plane) univ :=
        measure_mono (subset_univ _)
      simpa using h)
      (hmass₁ ▸ measure_mono hsub₁)
  have hμ₂copy : (μ₂ : Measure Plane) (affineMap ℓ z '' E) = 1 :=
    le_antisymm (by
      have h : (μ₂ : Measure Plane) (affineMap ℓ z '' E) ≤ (μ₂ : Measure Plane) univ :=
        measure_mono (subset_univ _)
      simpa using h)
      (hmass₂ ▸ measure_mono hsub₂)
  have hmass : weightedCrossDistanceMeasure μ₁ μ₂ univ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num)
      (weightedCrossDistanceMeasure_univ_bounds μ₁ μ₂
        hS₁.measurableSet hS₂.measurableSet hmass₁ hmass₂ hsep).1)
  have hAC : weightedCrossDistanceMeasure μ₁ μ₂ ≪ volume := by
    sorry
  exact (volume_distanceSet_affineMap_image_pos_iff hℓ z E).mp
    (volume_distanceSet_pos_of_weightedCrossDistanceMeasure_absolutelyContinuous
      μ₁ μ₂ hcopy hμ₁copy hμ₂copy hmass hAC)

end FalconerThetaGauge
