module

public import FalconerThetaGauge.Statement
public import FalconerThetaGauge.RadialProjectionSpread
public import FalconerThetaGauge.FilteredDistanceMeasureGeometry
public import FalconerThetaGauge.DistanceScaling
public import FalconerThetaGauge.RegularFilteredMeasureAbsoluteContinuity

/-!
# Theorem 1.1

The exact manuscript statement follows from genuine gauge preparation,
the proved space-splitting induction and summable Fourier reconstruction.
The weighted distance carrier and positive similarity transfer its conclusion
back to the original compact set.
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
  obtain ⟨ℓ, C, K, z, a, b, S₁, S₂, μ₁, μ₂, hℓ, hC, hK, hS₁, hS₂,
    hsub₁, hsub₂, hmass₁, hmass₂, _hsupp₁, _hsupp₂, hab, hball₁, hball₂,
    hsq₁, hsq₂, hsep, hgb₁, hgb₂, _henergy, hpin₁, hpin₂⟩ :=
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
  have hunit₁ : (μ₁ : Measure Plane) unitSquare = 1 :=
    le_antisymm (prob_le_one (μ := (μ₁ : Measure Plane)))
      (by simpa only [hmass₁] using
        (measure_mono (μ := (μ₁ : Measure Plane)) (hball₁.trans hsq₁)))
  have hunit₂ : (μ₂ : Measure Plane) unitSquare = 1 :=
    le_antisymm (prob_le_one (μ := (μ₂ : Measure Plane)))
      (by simpa only [hmass₂] using
        (measure_mono (μ := (μ₂ : Measure Plane)) (hball₂.trans hsq₂)))
  have hAC : weightedCrossDistanceMeasure μ₁ μ₂ ≪ volume :=
    weightedCrossDistanceMeasure_absolutelyContinuous μ₁ μ₂ hθ₀ hθ₁ hC hK.le hgb₁ hgb₂
      hunit₁ hunit₂ hab hS₁.measurableSet hS₂.measurableSet hmass₁ hmass₂ hball₁ hball₂
      (fun x hx ↦ (hpin₁ x hx).2) (fun y hy ↦ (hpin₂ y hy).2)
  exact (volume_distanceSet_affineMap_image_pos_iff hℓ z E).mp
    (volume_distanceSet_pos_of_weightedCrossDistanceMeasure_absolutelyContinuous
      μ₁ μ₂ hcopy hμ₁copy hμ₂copy hmass hAC)

end FalconerThetaGauge
