module

public import FalconerThetaGauge.DistanceLinearizationMassPassing

/-! # Genuine weighted and unweighted passing distance pushforwards -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The literal unweighted passing distance measure used in Estimate 7.7. -/
def passingUnweightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) : Measure ℝ :=
  (((ρ₁.restrict X).prod (ρ₂.restrict Y)).restrict Z).map
    (fun z : Plane × Plane ↦ dist z.1 z.2)

instance (ρ₁ ρ₂ : Measure Plane) [SFinite ρ₁] [SFinite ρ₂]
    (X Y : Set Plane) (Z : Set (Plane × Plane)) :
    SFinite (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
  unfold passingUnweightedDistanceMeasure
  infer_instance

instance (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (X Y : Set Plane) (Z : Set (Plane × Plane)) :
    IsFiniteMeasure (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
  unfold passingUnweightedDistanceMeasure
  infer_instance

theorem passingWeightedDistanceMeasure_eq_restricted_product (ρ₁ ρ₂ : Measure Plane)
    (X Y : Set Plane) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z) :
    passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z =
      ((((ρ₁.restrict X).prod (ρ₂.restrict Y)).restrict Z).withDensity
        crossDistanceWeight).map (fun z : Plane × Plane ↦ dist z.1 z.2) := by
  have heq : (fun z ↦ crossDistanceWeight z * ENNReal.ofReal (Z.indicator (fun _ ↦ 1) z)) =
      Z.indicator crossDistanceWeight := by
    ext z
    by_cases hz : z ∈ Z <;> simp [hz]
  rw [passingWeightedDistanceMeasure, filteredCrossDistanceMeasure, heq,
    withDensity_indicator hZ]

/-- The actual upper weight bound dominates the whole pushforward measure. -/
theorem passingWeightedDistanceMeasure_le_smul_unweighted (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] {X Y : Set Plane} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z) {W : ℝ≥0∞}
    (hW : ∀ x ∈ X, ∀ y ∈ Y, crossDistanceWeight (x, y) ≤ W) :
    passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z ≤
      W • passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z := by
  rw [passingWeightedDistanceMeasure_eq_restricted_product ρ₁ ρ₂ X Y hZ,
    passingUnweightedDistanceMeasure, ← Measure.map_smul _ continuous_dist.measurable.aemeasurable,
    ← withDensity_const]
  apply Measure.map_mono _ continuous_dist.measurable
  apply withDensity_mono
  filter_upwards [ae_restrict_of_ae (ae_restricted_product_carriers ρ₁ ρ₂ hX hY)] with z hz
  exact hW z.1 hz.1 z.2 hz.2

/-- The actual lower weight bound gives the reverse measure domination. -/
theorem smul_unweighted_le_passingWeightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] {X Y : Set Plane} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z) {W : ℝ≥0∞}
    (hW : ∀ x ∈ X, ∀ y ∈ Y, W ≤ crossDistanceWeight (x, y)) :
    W • passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z ≤
      passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z := by
  rw [passingWeightedDistanceMeasure_eq_restricted_product ρ₁ ρ₂ X Y hZ,
    passingUnweightedDistanceMeasure, ← Measure.map_smul _ continuous_dist.measurable.aemeasurable,
    ← withDensity_const]
  apply Measure.map_mono _ continuous_dist.measurable
  apply withDensity_mono
  filter_upwards [ae_restrict_of_ae (ae_restricted_product_carriers ρ₁ ρ₂ hX hY)] with z hz
  exact hW z.1 hz.1 z.2 hz.2

theorem ofReal_inv_sqrt_le_crossDistanceWeight {D : ℝ} (hD : 0 < D) {x y : Plane}
    (hxy : dist x y ≤ D) :
    ENNReal.ofReal ((Real.sqrt D)⁻¹) ≤ crossDistanceWeight (x, y) := by
  rw [ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 hD), crossDistanceWeight]
  exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hxy))

/-- Scalar collision mass scales exactly quadratically with the true measure. -/
theorem scalarCollisionMass_smul (η : Measure ℝ) [SFinite η] (c : ℝ≥0∞) (h u : ℝ) :
    scalarCollisionMass (c • η) (c • η) h u = c ^ (2 : ℕ) * scalarCollisionMass η η h u := by
  rw [scalarCollisionMass, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.smul_apply, smul_eq_mul, pow_two]
  rfl

theorem scalarCollisionMass_weighted_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z) {W : ℝ≥0∞}
    (hW : ∀ x ∈ X, ∀ y ∈ Y, crossDistanceWeight (x, y) ≤ W) (h u : ℝ) :
    scalarCollisionMass (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z)
        (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u ≤
      W ^ (2 : ℕ) * scalarCollisionMass (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z)
        (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u := by
  have hle := passingWeightedDistanceMeasure_le_smul_unweighted ρ₁ ρ₂ hX hY hZ hW
  let : SFinite (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
    rw [passingWeightedDistanceMeasure_eq_restricted_product ρ₁ ρ₂ X Y hZ]
    infer_instance
  rw [← scalarCollisionMass_smul]
  exact Measure.le_iff.1 (Measure.prod_mono hle hle) _ (measurableSet_scalarCollision h u)

theorem scalarCollisionMass_unweighted_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z) {W : ℝ≥0∞}
    (hW : ∀ x ∈ X, ∀ y ∈ Y, W ≤ crossDistanceWeight (x, y)) (h u : ℝ) :
    W ^ (2 : ℕ) * scalarCollisionMass (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z)
        (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u ≤
      scalarCollisionMass (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z)
        (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u := by
  have hle := smul_unweighted_le_passingWeightedDistanceMeasure ρ₁ ρ₂ hX hY hZ hW
  let : SFinite (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
    rw [passingWeightedDistanceMeasure_eq_restricted_product ρ₁ ρ₂ X Y hZ]
    infer_instance
  rw [← scalarCollisionMass_smul]
  exact Measure.le_iff.1 (Measure.prod_mono hle hle) _ (measurableSet_scalarCollision h u)

end FalconerThetaGauge
