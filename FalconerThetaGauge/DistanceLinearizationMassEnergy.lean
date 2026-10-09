module

public import FalconerThetaGauge.DistanceLinearizationMassWeighted

/-! # The actual unweighted collision mass and the weighted source distance energy -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem scalarCollisionMass_weighted_toReal_bounds (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z)
    {d D : ℝ} (hd : 0 < d) (hD : 0 < D)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y ∧ dist x y ≤ D) (h u : ℝ) :
    (scalarCollisionMass (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z)
        (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u).toReal / D ≤
        (scalarCollisionMass (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z)
          (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u).toReal ∧
      (scalarCollisionMass (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z)
        (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u).toReal ≤
        (scalarCollisionMass (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z)
          (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) h u).toReal / d := by
  have hW : ∀ x ∈ X, ∀ y ∈ Y,
      crossDistanceWeight (x, y) ≤ ENNReal.ofReal ((Real.sqrt d)⁻¹) :=
    fun x hx y hy ↦ crossDistanceWeight_le_of_dist hd (hsep x hx y hy).1
  let : IsFiniteMeasure (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) :=
    isFiniteMeasure_passingWeightedDistanceMeasure ρ₁ ρ₂ hX hY Z hW
  have hsq (r : ℝ) (hr : 0 < r) : ((Real.sqrt r)⁻¹) ^ (2 : ℕ) = r⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hr.le]
  constructor
  · have hle := scalarCollisionMass_unweighted_le ρ₁ ρ₂ hX hY hZ
      (fun x hx y hy ↦ ofReal_inv_sqrt_le_crossDistanceWeight hD (hsep x hx y hy).2) h u
    have hreal := ENNReal.toReal_mono (by unfold scalarCollisionMass; finiteness) hle
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (inv_nonneg.2 (Real.sqrt_nonneg D)), hsq D hD,
      div_eq_mul_inv, mul_comm] using hreal
  · have hle := scalarCollisionMass_weighted_le ρ₁ ρ₂ hX hY hZ hW h u
    have hreal := ENNReal.toReal_mono (by unfold scalarCollisionMass; finiteness) hle
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (inv_nonneg.2 (Real.sqrt_nonneg d)), hsq d hd,
      div_eq_mul_inv, mul_comm] using hreal

/-- The genuine unweighted counterpart of Definition 7.2, with the same carrier normalization. -/
def unweightedDistanceCollisionEnergy (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) (t : ℕ) : ℝ :=
  (2 : ℝ) ^ t / (ρ₁.real X * ρ₂.real Y) *
    (scalarCollisionMass (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z)
      (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) ((2 : ℝ) ^ (-(t : ℝ))) 0).toReal

theorem unweightedDistanceCollisionEnergy_nonneg (ρ₁ ρ₂ : Measure Plane)
    (X Y : Set Plane) (Z : Set (Plane × Plane)) (t : ℕ) :
    0 ≤ unweightedDistanceCollisionEnergy ρ₁ ρ₂ X Y Z t := by
  unfold unweightedDistanceCollisionEnergy
  positivity

/-- Both sides retain the actual singular weight, actual passing set, and actual carrier masses. -/
theorem maskedDistanceEnergy_unweighted_bounds (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z)
    {d D : ℝ} (hd : 0 < d) (hD : 0 < D)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y ∧ dist x y ≤ D) (t : ℕ) :
    unweightedDistanceCollisionEnergy ρ₁ ρ₂ X Y Z t / D ≤
        maskedDistanceEnergy ρ₁ ρ₂ X Y Z t ∧
      maskedDistanceEnergy ρ₁ ρ₂ X Y Z t ≤
        unweightedDistanceCollisionEnergy ρ₁ ρ₂ X Y Z t / d := by
  have h := scalarCollisionMass_weighted_toReal_bounds ρ₁ ρ₂ hX hY hZ hd hD hsep
    ((2 : ℝ) ^ (-(t : ℝ))) 0
  have hc : 0 ≤ (2 : ℝ) ^ t / (ρ₁.real X * ρ₂.real Y) := by positivity
  constructor
  · simpa only [unweightedDistanceCollisionEnergy, maskedDistanceEnergy,
      mul_div_assoc] using mul_le_mul_of_nonneg_left h.1 hc
  · simpa only [unweightedDistanceCollisionEnergy, maskedDistanceEnergy,
      mul_div_assoc] using mul_le_mul_of_nonneg_left h.2 hc

/-- On the actual source-separated cells, the weight comparison has the literal ratio `22`. -/
theorem maskedDistanceEnergy_cells_unweighted_bounds (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {a : ℕ} {A B : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) {Z : Set (Plane × Plane)} (hZ : MeasurableSet Z)
    (t : ℕ) :
    unweightedDistanceCollisionEnergy ρ₁ ρ₂ (dyadicCube a A) (dyadicCube a B) Z t /
        (11000 * dyadicRadius a) ≤
        maskedDistanceEnergy ρ₁ ρ₂ (dyadicCube a A) (dyadicCube a B) Z t ∧
      maskedDistanceEnergy ρ₁ ρ₂ (dyadicCube a A) (dyadicCube a B) Z t ≤
        unweightedDistanceCollisionEnergy ρ₁ ρ₂ (dyadicCube a A) (dyadicCube a B) Z t /
          (500 * dyadicRadius a) :=
  maskedDistanceEnergy_unweighted_bounds ρ₁ ρ₂
    (measurableSet_dyadicCube a A) (measurableSet_dyadicCube a B) hZ
    (mul_pos (by norm_num) (dyadicRadius_pos a))
    (mul_pos (by norm_num) (dyadicRadius_pos a))
    (fun _x hx _y hy ↦ dist_bounds_of_separatedDyadicCells hsep hx hy) t

end FalconerThetaGauge
