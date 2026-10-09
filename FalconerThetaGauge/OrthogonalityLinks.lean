module

public import FalconerThetaGauge.OrthogonalityGeometry
public import FalconerThetaGauge.FiniteGraphSchur

/-! # Actual cell-center links and the manuscript's phase separation -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped InnerProductSpace Classical

namespace FalconerThetaGauge

open GaugeFrostman

def orthogonalityArcScale (a p : ℕ) (E : ℝ) : ℝ :=
  min 1 (dyadicRadius p / dyadicRadius a * (2 : ℝ) ^ E)

def orthogonalityLinkThreshold (p : ℕ) (E : ℝ) : ℝ :=
  dyadicRadius p * (2 : ℝ) ^ (3 * E / 2)

theorem orthogonalityArcScale_pos (a p : ℕ) (E : ℝ) :
    0 < orthogonalityArcScale a p E :=
  lt_min (by norm_num) (mul_pos (div_pos (dyadicRadius_pos _) (dyadicRadius_pos _))
    (Real.rpow_pos_of_pos (by norm_num) _))

theorem orthogonalityArcScale_le_one (a p : ℕ) (E : ℝ) :
    orthogonalityArcScale a p E ≤ 1 := min_le_left _ _

theorem orthogonalityArcScale_mul_radius_le (a p : ℕ) (E : ℝ) :
    orthogonalityArcScale a p E * dyadicRadius a ≤ dyadicRadius p * (2 : ℝ) ^ E := by
  calc
    _ ≤ (dyadicRadius p / dyadicRadius a * (2 : ℝ) ^ E) * dyadicRadius a :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (dyadicRadius_pos _).le
    _ = _ := by field_simp [(dyadicRadius_pos a).ne']

theorem orthogonalityLinkThreshold_eq (p : ℕ) (E : ℝ) :
    orthogonalityLinkThreshold p E =
      dyadicRadius p * (2 : ℝ) ^ E * (2 : ℝ) ^ (E / 2) := by
  rw [orthogonalityLinkThreshold, mul_assoc, ← Real.rpow_add (by norm_num)]
  congr 2
  ring

theorem dyadicCellCenter_mem (p : ℕ) (P : Fin 2 → ℤ) :
    dyadicCellCenter p P ∈ dyadicCube p P := by
  intro i
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have he : (2 : ℝ) ^ p * dyadicCellCenter p P i = (P i : ℝ) + 1 / 2 := by
    change (2 : ℝ) ^ p * (((P i : ℝ) + 1 / 2) / (2 : ℝ) ^ p) = _
    exact mul_div_cancel₀ _ hp.ne'
  rw [he]
  constructor <;> linarith

/-- All three source linking inequalities, applied to the true dyadic cell centers. -/
def orthogonalityLinked (p : ℕ) (τ : ℝ) (w₁ w₂ : UnitCircle)
    (row col : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : Prop :=
  |inner ℝ (circleQuarterTurn w₁ : Plane)
    (dyadicCellCenter p row.1 - dyadicCellCenter p col.1)| ≤ τ ∧
  |inner ℝ (circleQuarterTurn w₂ : Plane)
    (dyadicCellCenter p row.2 - dyadicCellCenter p col.2)| ≤ τ ∧
  |inner ℝ (w₁ : Plane) (dyadicCellCenter p row.1 - dyadicCellCenter p col.1) +
    inner ℝ (w₂ : Plane) (dyadicCellCenter p row.2 - dyadicCellCenter p col.2)| ≤ τ

theorem orthogonalityLinked_symm (p : ℕ) (τ : ℝ) (w₁ w₂ : UnitCircle)
    {row col : (Fin 2 → ℤ) × (Fin 2 → ℤ)} :
    orthogonalityLinked p τ w₁ w₂ row col → orthogonalityLinked p τ w₁ w₂ col row := by
  have he (u : Plane) (x y : Plane) : inner ℝ u (y - x) = -inner ℝ u (x - y) := by
    rw [← neg_sub x y, inner_neg_right]
  intro h
  refine ⟨?_, ?_, ?_⟩
  · rw [he _ (dyadicCellCenter p row.1) (dyadicCellCenter p col.1), abs_neg]
    exact h.1
  · rw [he _ (dyadicCellCenter p row.2) (dyadicCellCenter p col.2), abs_neg]
    exact h.2.1
  · rw [he _ (dyadicCellCenter p row.1) (dyadicCellCenter p col.1),
      he _ (dyadicCellCenter p row.2) (dyadicCellCenter p col.2), ← neg_add, abs_neg]
    exact h.2.2

/-- The point-to-center error for any two nearby actual directions. -/
theorem dyadic_point_center_error {a p : ℕ} {X P P' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    {x x' : Plane} (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    {E : ℝ} (hE : 0 ≤ E) (w w₀ : UnitCircle)
    (hdir : ‖(w : Plane) - (w₀ : Plane)‖ ≤ orthogonalityArcScale a p E) :
    |inner ℝ (w : Plane) (x - x') -
      inner ℝ (w₀ : Plane) (dyadicCellCenter p P - dyadicCellCenter p P')| ≤
      3 * dyadicRadius p * (2 : ℝ) ^ E := by
  have hc := norm_sub_le_of_mem_same_dyadicCube
    (hP (dyadicCellCenter_mem p P)) (hP' (dyadicCellCenter_mem p P'))
  have herr := abs_inner_pair_sub_center_le x x' (dyadicCellCenter p P)
    (dyadicCellCenter p P') w w₀
  have hb : (1 : ℝ) ≤ (2 : ℝ) ^ E := Real.one_le_rpow (by norm_num) hE
  have hr := orthogonalityArcScale_mul_radius_le a p E
  have hs : ‖(w : Plane) - (w₀ : Plane)‖ *
      ‖dyadicCellCenter p P - dyadicCellCenter p P'‖ ≤
      3 / 2 * (dyadicRadius p * (2 : ℝ) ^ E) := by
    calc
      _ ≤ orthogonalityArcScale a p E * (3 / 2 * dyadicRadius a) :=
        mul_le_mul hdir hc (norm_nonneg _)
          (orthogonalityArcScale_pos a p E).le
      _ ≤ _ := by nlinarith
  have hx₀ := norm_sub_dyadicCellCenter_le hx
  have hx₁ := norm_sub_dyadicCellCenter_le hx'
  nlinarith [mul_nonneg (dyadicRadius_pos p).le (sub_nonneg.mpr hb)]

/-- The actual smoothed arc and actual dyadic cells incur at most `3·2^-p·2^E` error. -/
theorem orthogonality_point_center_error {a p : ℕ} {X P P' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    {x x' : Plane} (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    {E : ℝ} (hE : 0 ≤ E) (K : ℕ)
    (i : Fin (angularPartitionCount (orthogonalityArcScale a p E))) {w : UnitCircle}
    (hw : equalArcCutoff K (orthogonalityArcScale a p E) i w ≠ 0) :
    |inner ℝ (w : Plane) (x - x') -
      inner ℝ (angularDirection (equalAngularCellCenter
        (angularPartitionCount (orthogonalityArcScale a p E)) i))
        (dyadicCellCenter p P - dyadicCellCenter p P')| ≤
      3 * dyadicRadius p * (2 : ℝ) ^ E :=
  dyadic_point_center_error hP hP' hx hx' hE w
    (unitCircleOfAngle (equalAngularCellCenter _ i))
    (equalArcCutoff_norm_sub_center_le K (orthogonalityArcScale_pos a p E) i hw)

/-- A quarter turn preserves the exact same error bound for the angular phase derivative. -/
theorem orthogonality_point_center_perp_error {a p : ℕ} {X P P' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    {x x' : Plane} (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    {E : ℝ} (hE : 0 ≤ E) (K : ℕ)
    (i : Fin (angularPartitionCount (orthogonalityArcScale a p E))) {w : UnitCircle}
    (hw : equalArcCutoff K (orthogonalityArcScale a p E) i w ≠ 0) :
    |inner ℝ (circleQuarterTurn w : Plane) (x - x') -
      inner ℝ (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter
        (angularPartitionCount (orthogonalityArcScale a p E)) i)) : Plane)
        (dyadicCellCenter p P - dyadicCellCenter p P')| ≤
      3 * dyadicRadius p * (2 : ℝ) ^ E := by
  apply dyadic_point_center_error hP hP' hx hx' hE
  change ‖planeQuarterTurn (w : Plane) - planeQuarterTurn
    (unitCircleOfAngle (equalAngularCellCenter _ i) : Plane)‖ ≤ _
  rw [norm_planeQuarterTurn_sub]
  exact equalArcCutoff_norm_sub_center_le K (orthogonalityArcScale_pos a p E) i hw

end FalconerThetaGauge
