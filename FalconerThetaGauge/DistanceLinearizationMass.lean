module

public import FalconerThetaGauge.DistanceLinearizationCollision
public import FalconerThetaGauge.ScalarEnergyBinningShift

/-! # Actual one-cell collision mass after distance linearization -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- Regrouping four independent points preserves their actual product measure. -/
theorem measurePreserving_fourPointRegroup (μ ν : Measure Plane) [SFinite μ] [SFinite ν] :
    MeasurePreserving
      (fun z : (Plane × Plane) × (Plane × Plane) ↦ ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)) := by
  have h₁ := measurePreserving_prodAssoc μ ν (μ.prod ν)
  have h₂ := (MeasurePreserving.id μ).prod
    ((measurePreserving_prodAssoc ν μ ν).symm MeasurableEquiv.prodAssoc)
  have h₃ := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).prod (MeasurePreserving.id ν))
  have h₄ := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν)
  have h₅ := (measurePreserving_prodAssoc μ μ (ν.prod ν)).symm MeasurableEquiv.prodAssoc
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

def projectionShiftedPairMass (ν : Measure Plane) (w : UnitCircle) (h u : ℝ) : ℝ≥0∞ :=
  ν.prod ν {z | |inner ℝ (w : Plane) (z.1 - z.2) - u| ≤ h}

theorem projectionShiftedPairMass_eq_scalarCollision (ν : Measure Plane) [SFinite ν]
    (w : UnitCircle) (h u : ℝ) :
    projectionShiftedPairMass ν w h u =
      scalarCollisionMass (ν.map (fun y ↦ inner ℝ (w : Plane) y))
        (ν.map (fun y ↦ inner ℝ (w : Plane) y)) h u := by
  rw [scalarCollisionMass, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (measurableSet_scalarCollision h u)]
  simp only [projectionShiftedPairMass, inner_sub_right, preimage_ofPred_eq, Prod.map]

/-- Literal shifted projection coincidences satisfy Lemma 7.3(i). -/
theorem projectionShiftedPairMass_le_four (ν : Measure Plane) [IsFiniteMeasure ν]
    (w : UnitCircle) {h : ℝ} (hh : 0 < h) (u : ℝ) :
    projectionShiftedPairMass ν w h u ≤ 4 * projectionShiftedPairMass ν w h 0 := by
  rw [projectionShiftedPairMass_eq_scalarCollision, projectionShiftedPairMass_eq_scalarCollision]
  exact scalarCollisionMass_shift_le_four _ hh u

/-- The actual distance-pushforward collision is the regrouped four-point event. -/
theorem scalarCollisionMass_crossDistance_eq_regrouped (μ ν : Measure Plane)
    [SFinite μ] [SFinite ν] (h : ℝ) :
    scalarCollisionMass (crossDistanceMeasure μ ν) (crossDistanceMeasure μ ν) h 0 =
      ((μ.prod μ).prod (ν.prod ν))
        {z | |dist z.1.1 z.2.1 - dist z.1.2 z.2.2| ≤ h} := by
  rw [scalarCollisionMass, crossDistanceMeasure,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (measurableSet_scalarCollision h 0)]
  have hreg := measurePreserving_fourPointRegroup μ ν
  rw [← hreg.map_eq, Measure.map_apply hreg.measurable]
  · simp only [preimage_ofPred_eq, Prod.map, sub_zero]
  · exact (isClosed_le (by fun_prop) continuous_const).measurableSet

def projectionFourPointCollisionMass (μ ν : Measure Plane) (w : UnitCircle) (h : ℝ) : ℝ≥0∞ :=
  ((μ.prod μ).prod (ν.prod ν))
    {z | |inner ℝ (w : Plane) (z.1.1 - z.1.2) -
      inner ℝ (w : Plane) (z.2.1 - z.2.2)| ≤ h}

/-- Tonelli and the genuine shifted-collision estimate bound every source pair. -/
theorem projectionFourPointCollisionMass_le_four (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (w : UnitCircle) {h : ℝ} (hh : 0 < h) :
    projectionFourPointCollisionMass μ ν w h ≤
      4 * (μ univ) ^ (2 : ℕ) * projectionShiftedPairMass ν w h 0 := by
  have hm : MeasurableSet {z : (Plane × Plane) × (Plane × Plane) |
      |inner ℝ (w : Plane) (z.1.1 - z.1.2) -
        inner ℝ (w : Plane) (z.2.1 - z.2.2)| ≤ h} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  rw [projectionFourPointCollisionMass, Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ _z, 4 * projectionShiftedPairMass ν w h 0 ∂μ.prod μ := by
      apply lintegral_mono
      intro z
      simpa only [projectionShiftedPairMass, preimage_ofPred_eq, abs_sub_comm] using
        projectionShiftedPairMass_le_four ν w hh (inner ℝ (w : Plane) (z.1 - z.2))
    _ = _ := by
      rw [lintegral_const, ← univ_prod_univ, Measure.prod_prod]
      ring

/-- The actual cell-distance collision is bounded by its genuine four-point projection event. -/
theorem scalarCollisionMass_crossDistance_cells_le_projection (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {a p t : ℕ} {A B P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) (hP : dyadicCube p P ⊆ dyadicCube a A)
    (hQ : dyadicCube p Q ⊆ dyadicCube a B) (hdepth : a + t < 2 * p)
    {h : ℝ} (hh : 2 * (2 : ℝ) ^ (-(t : ℝ)) ≤ h) :
    scalarCollisionMass
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        (crossDistanceMeasure (ρ.restrict (dyadicCube p P)) (ρ.restrict (dyadicCube p Q)))
        ((2 : ℝ) ^ (-(t : ℝ))) 0 ≤
      projectionFourPointCollisionMass (ρ.restrict (dyadicCube p P))
        (ρ.restrict (dyadicCube p Q))
        (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q)) h := by
  rw [scalarCollisionMass_crossDistance_eq_regrouped, projectionFourPointCollisionMass]
  apply measure_mono_ae
  have hd : MeasurableSet {z : (Plane × Plane) × (Plane × Plane) |
      |dist z.1.1 z.2.1 - dist z.1.2 z.2.2| ≤ (2 : ℝ) ^ (-(t : ℝ))} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hm : MeasurableSet {z : (Plane × Plane) × (Plane × Plane) |
      |inner ℝ (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q) : Plane)
          (z.1.1 - z.1.2) -
        inner ℝ (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q) : Plane)
          (z.2.1 - z.2.2)| ≤ h} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  apply (Measure.ae_prod_iff_ae_ae (hd.imp hm)).2
  filter_upwards [ae_restricted_product_carriers ρ ρ
    (measurableSet_dyadicCube p P) (measurableSet_dyadicCube p P)] with x hx
  filter_upwards [ae_restricted_product_carriers ρ ρ
    (measurableSet_dyadicCube p Q) (measurableSet_dyadicCube p Q)] with y hy
  intro hcollision
  exact (distance_collision_projection_collision_cells hsep hP hQ hdepth
    hx.1 hx.2 hy.1 hy.2 hcollision).trans hh

end FalconerThetaGauge
