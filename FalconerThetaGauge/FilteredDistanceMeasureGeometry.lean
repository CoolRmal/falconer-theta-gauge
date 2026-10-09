module

public import FalconerThetaGauge.FilteredDistanceMeasure

/-!
# Bounds and reconstruction for the actual weighted distance measure

The rational constants below are exactly the source's `0.24`, `0.26`, and
`2.1`. The diagonal singularity is retained and excluded only through the
actual separated-carrier hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerThetaGauge

theorem crossDistanceWeight_le_two_point_one {x y : Plane}
    (hsep : (24 / 100 : ℝ) ≤ dist x y) :
    crossDistanceWeight (x, y) ≤ ENNReal.ofReal (21 / 10) := by
  have hd : 0 < dist x y := lt_of_lt_of_le (by norm_num) hsep
  have hs : 0 < Real.sqrt (dist x y) := Real.sqrt_pos.2 hd
  have hlower : (10 / 21 : ℝ) ≤ Real.sqrt (dist x y) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  rw [crossDistanceWeight_eq_ofReal (dist_pos.mp hd)]
  apply ENNReal.ofReal_le_ofReal
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10 / 21) hlower
  simpa using hi

theorem one_le_crossDistanceWeight {x y : Plane} (hd : dist x y ≤ 1) :
    1 ≤ crossDistanceWeight (x, y) := by
  have hs : ENNReal.ofReal (Real.sqrt (dist x y)) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (Real.sqrt_le_one.2 hd)
  simpa [crossDistanceWeight] using ENNReal.inv_le_inv.mpr hs

/-- Carrier information is used on the actual product probability. -/
theorem ae_product_carriers (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S₁ S₂ : Set Plane} (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂)
    (hμ : μ S₁ = 1) (hν : ν S₂ = 1) :
    ∀ᵐ p ∂μ.prod ν, p.1 ∈ S₁ ∧ p.2 ∈ S₂ := by
  apply (ae_mem_iff_measure_eq (h₁.prod h₂).nullMeasurableSet).2
  simp [Measure.prod_prod, hμ, hν]

theorem weightedCrossDistanceMeasure_univ_bounds (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S₁ S₂ : Set Plane} (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂)
    (hμ : μ S₁ = 1) (hν : ν S₂ = 1)
    (hsep : ∀ x ∈ S₁, ∀ y ∈ S₂,
      (24 / 100 : ℝ) ≤ dist x y ∧ dist x y ≤ 26 / 100) :
    1 ≤ weightedCrossDistanceMeasure μ ν univ ∧
      weightedCrossDistanceMeasure μ ν univ ≤ ENNReal.ofReal (21 / 10) := by
  have hc := ae_product_carriers μ ν h₁ h₂ hμ hν
  constructor
  · rw [weightedCrossDistanceMeasure_univ]
    have h : ∀ᵐ p ∂μ.prod ν, 1 ≤ crossDistanceWeight p := by
      filter_upwards [hc] with p hp
      exact one_le_crossDistanceWeight (by linarith [(hsep p.1 hp.1 p.2 hp.2).2])
    simpa using lintegral_mono_ae h
  · apply weightedCrossDistanceMeasure_univ_le
    filter_upwards [hc] with p hp
    exact crossDistanceWeight_le_two_point_one (hsep p.1 hp.1 p.2 hp.2).1

theorem isFiniteMeasure_weightedCrossDistanceMeasure (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {W : ℝ≥0∞} (hWfin : W ≠ ∞)
    (hW : ∀ᵐ p ∂μ.prod ν, crossDistanceWeight p ≤ W) :
    IsFiniteMeasure (weightedCrossDistanceMeasure μ ν) := by
  exact ⟨(weightedCrossDistanceMeasure_univ_le μ ν hW).trans_lt hWfin.lt_top⟩

/-- Every dominated actual filter is finite when the weighted source is finite. -/
theorem isFiniteMeasure_filteredCrossDistanceMeasure (μ ν : Measure Plane)
    [IsFiniteMeasure (weightedCrossDistanceMeasure μ ν)] {m : Plane × Plane → ℝ}
    (hm : ∀ᵐ p ∂μ.prod ν, m p ≤ 1) :
    IsFiniteMeasure (filteredCrossDistanceMeasure μ ν m) :=
  isFiniteMeasure_of_le (weightedCrossDistanceMeasure μ ν)
    (filteredCrossDistanceMeasure_le μ ν hm)

/-- The actual weighted distance measure is carried by the exact target distance set. -/
theorem weightedCrossDistanceMeasure_distanceSet_eq_univ
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Plane} (hE : IsCompact E) (hμ : μ E = 1) (hν : ν E = 1) :
    weightedCrossDistanceMeasure μ ν (distanceSet E) =
      weightedCrossDistanceMeasure μ ν univ := by
  have hc := ae_product_carriers μ ν hE.measurableSet hE.measurableSet hμ hν
  have ha : ∀ᵐ p ∂(μ.prod ν).withDensity crossDistanceWeight,
      dist p.1 p.2 ∈ distanceSet E := by
    filter_upwards [(withDensity_absolutelyContinuous (μ.prod ν) crossDistanceWeight).ae_le hc]
      with p hp
    exact ⟨p, hp, rfl⟩
  rw [weightedCrossDistanceMeasure, Measure.map_apply continuous_dist.measurable
    (measurableSet_distanceSet hE), Measure.map_apply continuous_dist.measurable
    MeasurableSet.univ, preimage_univ]
  apply measure_congr
  exact eventuallyEqSet_univ.2 ha

/-- Multiplying by an actual pair mask preserves the exact distance carrier. -/
theorem filteredCrossDistanceMeasure_distanceSet_eq_univ
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : Plane × Plane → ℝ) {E : Set Plane}
    (hE : IsCompact E) (hμ : μ E = 1) (hν : ν E = 1) :
    filteredCrossDistanceMeasure μ ν m (distanceSet E) =
      filteredCrossDistanceMeasure μ ν m univ := by
  have hc := ae_product_carriers μ ν hE.measurableSet hE.measurableSet hμ hν
  have ha : ∀ᵐ p ∂(μ.prod ν).withDensity
      (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (m p)),
      dist p.1 p.2 ∈ distanceSet E := by
    filter_upwards [(withDensity_absolutelyContinuous (μ.prod ν)
      (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (m p))).ae_le hc] with p hp
    exact ⟨p, hp, rfl⟩
  rw [filteredCrossDistanceMeasure, Measure.map_apply continuous_dist.measurable
    (measurableSet_distanceSet hE), Measure.map_apply continuous_dist.measurable
    MeasurableSet.univ, preimage_univ]
  exact measure_congr (eventuallyEqSet_univ.2 ha)

/-- A nonzero absolutely continuous weighted distance measure proves positive length. -/
theorem volume_distanceSet_pos_of_weightedCrossDistanceMeasure_absolutelyContinuous
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Plane} (hE : IsCompact E) (hμ : μ E = 1) (hν : ν E = 1)
    (hmass : weightedCrossDistanceMeasure μ ν univ ≠ 0)
    (hAC : weightedCrossDistanceMeasure μ ν ≪ volume) :
    0 < volume (distanceSet E) := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  exact hmass ((weightedCrossDistanceMeasure_distanceSet_eq_univ μ ν hE hμ hν).symm.trans
    (hAC hzero))

/-- Absolute continuity of one nonzero actual filtered measure is enough for positive length. -/
theorem volume_distanceSet_pos_of_filteredCrossDistanceMeasure_absolutelyContinuous
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : Plane × Plane → ℝ) {E : Set Plane}
    (hE : IsCompact E) (hμ : μ E = 1) (hν : ν E = 1)
    (hmass : filteredCrossDistanceMeasure μ ν m univ ≠ 0)
    (hAC : filteredCrossDistanceMeasure μ ν m ≪ volume) :
    0 < volume (distanceSet E) := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  exact hmass ((filteredCrossDistanceMeasure_distanceSet_eq_univ μ ν m hE hμ hν).symm.trans
    (hAC hzero))

end FalconerThetaGauge
