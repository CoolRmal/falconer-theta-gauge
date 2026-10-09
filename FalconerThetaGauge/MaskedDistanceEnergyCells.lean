module

public import FalconerThetaGauge.MaskedDistanceEnergyTests
public import FalconerThetaGauge.DirectionalTestsAverageGridCount

/-! # The literal separated dyadic-cell geometry and distance-energy bound (7.2) -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The paper's exact center-separation convention, with `K=1000`. -/
def SeparatedDyadicCells (a : ℕ) (P Q : Fin 2 → ℤ) : Prop :=
  1000 * dyadicRadius a ≤ dist (dyadicCellCenter a P) (dyadicCellCenter a Q) ∧
    dist (dyadicCellCenter a P) (dyadicCellCenter a Q) ≤ 10000 * dyadicRadius a

/-- Every actual point pair in source-separated cells has the claimed separation range. -/
theorem dist_bounds_of_separatedDyadicCells {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) {x y : Plane}
    (hx : x ∈ dyadicCube a P) (hy : y ∈ dyadicCube a Q) :
    500 * dyadicRadius a ≤ dist x y ∧ dist x y ≤ 11000 * dyadicRadius a := by
  have hrad : 0 < dyadicRadius a := dyadicRadius_pos a
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hbound {R : Fin 2 → ℤ} {z : Plane} (hz : z ∈ dyadicCube a R) :
      dist z (dyadicCellCenter a R) ≤ 2 * dyadicRadius a := by
    apply (dist_le_of_mem_dyadicCube hz (dyadicCellCenter_mem_dyadicCube a R)).trans
    rw [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hsqrt (by positivity)
  have hx' := hbound hx
  have hy' := hbound hy
  constructor
  · have htri := (dist_triangle (dyadicCellCenter a P) x (dyadicCellCenter a Q)).trans
      (add_le_add le_rfl (dist_triangle x y (dyadicCellCenter a Q)))
    rw [dist_comm (dyadicCellCenter a P) x] at htri
    linarith [hsep.1]
  · have htri := (dist_triangle x (dyadicCellCenter a P) y).trans
      (add_le_add le_rfl (dist_triangle (dyadicCellCenter a P) (dyadicCellCenter a Q) y))
    rw [dist_comm (dyadicCellCenter a Q) y] at htri
    linarith [hsep.2]

/-- The true energy bound from any positive carrier separation, with no test-energy assumption. -/
theorem maskedDistanceEnergy_le_of_separation (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) (Z : Set (Plane × Plane)) (t : ℕ) :
    maskedDistanceEnergy ρ₁ ρ₂ X Y Z t ≤
      (2 : ℝ) ^ t / d * (ρ₁.real X * ρ₂.real Y) := by
  have hsq : (Real.sqrt d)⁻¹ ^ (2 : ℕ) = d⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hd.le]
  have h := maskedDistanceEnergy_le ρ₁ ρ₂ hX hY Z
    (inv_nonneg.mpr (Real.sqrt_nonneg d))
    (fun x hx y hy ↦ crossDistanceWeight_le_of_dist hd (hsep x hx y hy)) t
  simpa only [hsq, div_eq_mul_inv] using h

/-- The first half of source (7.2), on the actual separated cells and true passing measure. -/
theorem maskedDistanceEnergy_cells_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) (Z : Set (Plane × Plane)) (t : ℕ) :
    maskedDistanceEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q) Z t ≤
      (2 : ℝ) ^ (t + a) * (ρ₁.real (dyadicCube a P) * ρ₂.real (dyadicCube a Q)) := by
  have hpoint : ∀ x ∈ dyadicCube a P, ∀ y ∈ dyadicCube a Q, dyadicRadius a ≤ dist x y := by
    intro x hx y hy
    have h := (dist_bounds_of_separatedDyadicCells hsep hx hy).1
    linarith [dyadicRadius_pos a]
  have h := maskedDistanceEnergy_le_of_separation ρ₁ ρ₂
    (measurableSet_dyadicCube a P) (measurableSet_dyadicCube a Q)
    (dyadicRadius_pos a) hpoint Z t
  simpa only [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
    div_eq_mul_inv, inv_inv, pow_add] using h

/-- The literal passing distance measure is carried by the source's exact distance interval. -/
theorem passingWeightedDistanceMeasure_cells_carrier (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) (Z : Set (Plane × Plane)) :
    passingWeightedDistanceMeasure ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q) Z
        (Icc (500 * dyadicRadius a) (11000 * dyadicRadius a)) =
      passingWeightedDistanceMeasure ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q) Z univ :=
  passingWeightedDistanceMeasure_carrier ρ₁ ρ₂
    (measurableSet_dyadicCube a P) (measurableSet_dyadicCube a Q) Z measurableSet_Icc
    (fun _x hx _y hy ↦ dist_bounds_of_separatedDyadicCells hsep hx hy)

/-- The second half of source (7.2), expressed in the actual excess of the actual measure. -/
theorem maskedDistanceEnergy_cells_le_excess (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N) {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) (Z : Set (Plane × Plane)) (t : ℕ) :
    maskedDistanceEnergy ρ ρ (dyadicCube a P) (dyadicCube a Q) Z t ≤
      (2 : ℝ) ^ ((t : ℝ) - a) * (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N a) := by
  have hmass : ρ.real (dyadicCube a P) * ρ.real (dyadicCube a Q) ≤ maxCellMass ρ a ^ 2 := by
    simpa only [unitCellWeight, pow_two] using mul_le_mul
      (unitCellWeight_le_maxCellMass_all ρ hρ a P) (unitCellWeight_le_maxCellMass_all ρ hρ a Q)
      measureReal_nonneg (maxCellMass_nonneg ρ a)
  calc
    _ ≤ (2 : ℝ) ^ (t + a) * maxCellMass ρ a ^ 2 :=
      (maskedDistanceEnergy_cells_le ρ ρ hsep Z t).trans
        (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = _ := by
      rw [maxCellMass_eq_power_excess ρ hρ hN a, ← Real.rpow_natCast, pow_two]
      simp only [Nat.cast_add, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end FalconerThetaGauge
