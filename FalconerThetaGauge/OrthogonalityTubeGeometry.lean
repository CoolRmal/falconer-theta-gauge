module

public import FalconerThetaGauge.OrthogonalityPhaseSeparation

/-! # Linked columns in one ancestor group lie in the witness's genuine tube -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped InnerProductSpace Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem directionLineResidual_norm_eq_abs_inner_quarterTurn (c z : Plane) (w : UnitCircle) :
    ‖directionLineResidual c w z‖ = |inner ℝ (z - c) (circleQuarterTurn w : Plane)| := by
  have hq : (circleQuarterTurn w : Plane) = angularDirection (circleAngle w + Real.pi / 2) := by
    simpa only [unitCircleOfAngle_circleAngle, coe_unitCircleOfAngle] using
      congrArg Subtype.val (circleQuarterTurn_unitCircleOfAngle (circleAngle w))
  have hh := directionLineResidual_norm_eq_abs_inner_quarterAngle c z (circleAngle w)
  simpa only [unitCircleOfAngle_circleAngle, ← hq] using hh

theorem abs_inner_change_direction_le (v : Plane) (w w₀ : UnitCircle) :
    |inner ℝ (circleQuarterTurn w : Plane) v -
      inner ℝ (circleQuarterTurn w₀ : Plane) v| ≤
      ‖(w : Plane) - (w₀ : Plane)‖ * ‖v‖ := by
  rw [← inner_sub_left]
  simpa only [circleQuarterTurn, norm_planeQuarterTurn_sub] using
    abs_real_inner_le_norm (planeQuarterTurn w - planeQuarterTurn w₀) v

theorem linked_witness_line_distance_le {c z z₀ : Plane} {w w₀ : UnitCircle} {τ ℓ : ℝ}
    (hz : |inner ℝ (circleQuarterTurn w₀ : Plane) (z - c)| ≤ τ)
    (hz₀ : |inner ℝ (circleQuarterTurn w₀ : Plane) (z₀ - c)| ≤ τ)
    (hdir : ‖(w : Plane) - (w₀ : Plane)‖ ≤ ℓ) :
    ‖directionLineResidual z₀ w z‖ ≤ 2 * τ + ℓ * ‖z - z₀‖ := by
  rw [directionLineResidual_norm_eq_abs_inner_quarterTurn, real_inner_comm]
  have he : inner ℝ (circleQuarterTurn w₀ : Plane) (z - z₀) =
      inner ℝ (circleQuarterTurn w₀ : Plane) (z - c) -
      inner ℝ (circleQuarterTurn w₀ : Plane) (z₀ - c) := by
    simp only [inner_sub_right]
    ring
  have hcenter : |inner ℝ (circleQuarterTurn w₀ : Plane) (z - z₀)| ≤ 2 * τ := by
    rw [he]
    have hh := abs_add_le (inner ℝ (circleQuarterTurn w₀ : Plane) (z - c))
      (-inner ℝ (circleQuarterTurn w₀ : Plane) (z₀ - c))
    rw [abs_neg, ← sub_eq_add_neg] at hh
    linarith
  have hchange := (abs_inner_change_direction_le (z - z₀) w w₀).trans
    (mul_le_mul_of_nonneg_right hdir (norm_nonneg _))
  have hh := abs_sub_abs_le_abs_sub
    (inner ℝ (circleQuarterTurn w : Plane) (z - z₀))
    (inner ℝ (circleQuarterTurn w₀ : Plane) (z - z₀))
  linarith

theorem linked_witness_width_budget {a g p : ℕ} (hag : a ≤ g) {E : ℝ}
    (hlarge : 12 ≤ (2 : ℝ) ^ (E / 2)) :
    2 * orthogonalityLinkThreshold p E +
      orthogonalityArcScale a p E * (3 / 2 * dyadicRadius g) <
      dyadicRadius p * (2 : ℝ) ^ (2 * E) := by
  have hrad : dyadicRadius g ≤ dyadicRadius a := by
    unfold dyadicRadius
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact neg_le_neg (by exact_mod_cast hag)
  have hℓ := orthogonalityArcScale_mul_radius_le a p E
  have hterm : orthogonalityArcScale a p E * (3 / 2 * dyadicRadius g) ≤
      3 / 2 * (dyadicRadius p * (2 : ℝ) ^ E) := by
    have hh := mul_le_mul_of_nonneg_left hrad (orthogonalityArcScale_pos a p E).le
    nlinarith
  have hpow : (2 : ℝ) ^ E = ((2 : ℝ) ^ (E / 2)) ^ (2 : ℕ) := by
    calc
      _ = (2 : ℝ) ^ ((E / 2) * (2 : ℝ)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_mul (by norm_num), Real.rpow_two]
  have he : (2 : ℝ) ^ (2 * E) = ((2 : ℝ) ^ E) ^ (2 : ℕ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_two]
  rw [orthogonalityLinkThreshold_eq, he]
  have hpoly : 2 * (2 : ℝ) ^ (E / 2) + 3 / 2 < (2 : ℝ) ^ E := by
    rw [hpow]
    nlinarith
  have hh := mul_lt_mul_of_pos_left hpoly
    (mul_pos (dyadicRadius_pos p)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) E))
  nlinarith

/-- The linked centers in one genuine ancestor group enter the actual passing witness tube. -/
theorem linked_centers_mem_witness_tube {a g p : ℕ} (hag : a ≤ g) {E : ℝ}
    (hlarge : 12 ≤ (2 : ℝ) ^ (E / 2)) {G P P₀ : Fin 2 → ℤ}
    (hP : dyadicCellCenter p P ∈ dyadicCube g G)
    (hP₀ : dyadicCellCenter p P₀ ∈ dyadicCube g G) {c : Plane} {w₀ : UnitCircle}
    (hc : |inner ℝ (circleQuarterTurn w₀ : Plane) (dyadicCellCenter p P - c)| ≤
      orthogonalityLinkThreshold p E)
    (hc₀ : |inner ℝ (circleQuarterTurn w₀ : Plane) (dyadicCellCenter p P₀ - c)| ≤
      orthogonalityLinkThreshold p E) {w : UnitCircle}
    (hdir : ‖(w : Plane) - (w₀ : Plane)‖ ≤ orthogonalityArcScale a p E)
    {width : ℝ} (hwidth : 1 ≤ width) :
    dyadicCellCenter p P ∈ directionalTube g p E width (dyadicCellCenter p P₀) w := by
  have hd := norm_sub_le_of_mem_same_dyadicCube hP hP₀
  have hline := linked_witness_line_distance_le hc hc₀ hdir
  have hbudget := linked_witness_width_budget (p := p) hag hlarge
  constructor
  · have hδ := mul_le_mul_of_nonneg_left hd (orthogonalityArcScale_pos a p E).le
    have hw := mul_le_mul_of_nonneg_right hwidth
      (mul_nonneg (dyadicRadius_pos p).le
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * E)).le)
    change ‖directionLineResidual (dyadicCellCenter p P₀) w (dyadicCellCenter p P)‖ ≤
      width * dyadicRadius p * (2 : ℝ) ^ (2 * E)
    nlinarith
  · change ‖dyadicCellCenter p P - dyadicCellCenter p P₀‖ ≤ 4 * dyadicRadius g
    nlinarith [dyadicRadius_pos g]

end FalconerThetaGauge
