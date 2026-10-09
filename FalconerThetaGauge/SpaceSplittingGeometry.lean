module

public import FalconerThetaGauge.SpaceSplittingNearCells
public import FalconerThetaGauge.MaskedDistanceEnergyCells

/-! # Literal near/far and separated-depth geometry in source Estimate 7.8 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem dyadicRadius_antitone : Antitone dyadicRadius := by
  intro p q hpq
  unfold dyadicRadius
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (by exact_mod_cast hpq)

theorem dyadicRadius_add (p q : ℕ) :
    dyadicRadius (p + q) = dyadicRadius p * dyadicRadius q := by
  unfold dyadicRadius
  rw [Nat.cast_add, neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- Replacing both points by their actual dyadic centers costs at most `3/2` cell sides. -/
theorem dist_dyadicCenters_le_point_dist {p : ℕ} {P Q : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q) :
    dist (dyadicCellCenter p P) (dyadicCellCenter p Q) ≤
      dist x y + 3 / 2 * dyadicRadius p := by
  have h₁ := dist_triangle (dyadicCellCenter p P) x (dyadicCellCenter p Q)
  have h₂ := dist_triangle x y (dyadicCellCenter p Q)
  have hx' := norm_sub_dyadicCellCenter_le hx
  have hy' := norm_sub_dyadicCellCenter_le hy
  rw [← dist_eq_norm] at hx' hy'
  rw [dist_comm (dyadicCellCenter p P) x] at h₁
  linarith

theorem dist_points_le_dyadicCenters {p : ℕ} {P Q : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q) :
    dist x y ≤ dist (dyadicCellCenter p P) (dyadicCellCenter p Q) +
      3 / 2 * dyadicRadius p := by
  have h₁ := dist_triangle x (dyadicCellCenter p P) y
  have h₂ := dist_triangle (dyadicCellCenter p P) (dyadicCellCenter p Q) y
  have hx' := norm_sub_dyadicCellCenter_le hx
  have hy' := norm_sub_dyadicCellCenter_le hy
  rw [← dist_eq_norm] at hx' hy'
  rw [dist_comm (dyadicCellCenter p Q) y] at h₂
  linarith

/-- Every genuine far term has `max(dx,dy) > 2.5·2⁻ʰ`, as in the source proof. -/
theorem spaceSplittingFar_distance_gt {p : ℕ}
    {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} {x x' y y' : Plane}
    (hfar : ¬spaceSplittingNear p R S)
    (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2) :
    5 / 2 * dyadicRadius p < max (dist x x') (dist y y') := by
  by_contra h
  have hh := le_of_not_gt h
  apply hfar
  constructor
  · linarith [dist_dyadicCenters_le_point_dist hx hx', le_max_left (dist x x') (dist y y')]
  · linarith [dist_dyadicCenters_le_point_dist hy hy', le_max_right (dist x x') (dist y y')]

/-- In Case B both stationary phases have the source's positive lower bound. -/
theorem spaceSplittingFar_comparable_distance_gt {p : ℕ}
    {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} {x x' y y' : Plane}
    (hfar : ¬spaceSplittingNear p R S)
    (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2)
    (hcase : max (dist x x') (dist y y') ≤ 2 * min (dist x x') (dist y y')) :
    5 / 4 * dyadicRadius p < dist x x' ∧
      5 / 4 * dyadicRadius p < dist y y' := by
  have hmax := spaceSplittingFar_distance_gt hfar hx hx' hy hy'
  constructor
  · linarith [min_le_left (dist x x') (dist y y')]
  · linarith [min_le_right (dist x x') (dist y y')]

/-- Source depth bins imply true separation of the literal half-open dyadic cells. -/
theorem separatedDyadicCells_of_distance_bin {n : ℕ} {P Q : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube n P) (hy : y ∈ dyadicCube n Q)
    (hlow : 2000 * dyadicRadius n < dist x y)
    (hupper : dist x y ≤ 8000 * dyadicRadius n) : SeparatedDyadicCells n P Q := by
  have hr := dyadicRadius_pos n
  constructor
  · linarith [dist_points_le_dyadicCenters hx hy]
  · linarith [dist_dyadicCenters_le_point_dist hx hy]

/-- The comparable source distance bin yields separated cell pairs on both sides. -/
theorem spaceSplitting_comparable_bin_separated {n : ℕ} {P P' Q Q' : Fin 2 → ℤ}
    {x x' y y' : Plane} (hx : x ∈ dyadicCube n P) (hx' : x' ∈ dyadicCube n P')
    (hy : y ∈ dyadicCube n Q) (hy' : y' ∈ dyadicCube n Q')
    (hcase : max (dist x x') (dist y y') ≤ 2 * min (dist x x') (dist y y'))
    (hlow : 4000 * dyadicRadius n < max (dist x x') (dist y y'))
    (hupper : max (dist x x') (dist y y') ≤ 8000 * dyadicRadius n) :
    SeparatedDyadicCells n P P' ∧ SeparatedDyadicCells n Q Q' := by
  constructor
  · exact separatedDyadicCells_of_distance_bin hx hx'
      (by linarith [min_le_left (dist x x') (dist y y')])
      ((le_max_left _ _).trans hupper)
  · exact separatedDyadicCells_of_distance_bin hy hy'
      (by linarith [min_le_right (dist x x') (dist y y')])
      ((le_max_right _ _).trans hupper)

/-- Only the source range `a<n<h+12` can occur for actual far pairs in the root cells. -/
theorem spaceSplitting_distance_bin_depth_bounds {a p n : ℕ}
    {A B : Fin 2 → ℤ} {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} {x x' y y' : Plane}
    (hfar : ¬spaceSplittingNear p R S)
    (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2)
    (hxA : x ∈ dyadicCube a A) (hxA' : x' ∈ dyadicCube a A)
    (hyB : y ∈ dyadicCube a B) (hyB' : y' ∈ dyadicCube a B)
    (hlow : 4000 * dyadicRadius n < max (dist x x') (dist y y'))
    (hupper : max (dist x x') (dist y y') ≤ 8000 * dyadicRadius n) :
    a < n ∧ n < p + 12 := by
  have hroot : max (dist x x') (dist y y') ≤ 3 / 2 * dyadicRadius a := by
    apply max_le
    · simpa only [dist_eq_norm] using norm_sub_le_of_mem_same_dyadicCube hxA hxA'
    · simpa only [dist_eq_norm] using norm_sub_le_of_mem_same_dyadicCube hyB hyB'
  have hfar' := spaceSplittingFar_distance_gt hfar hx hx' hy hy'
  constructor
  · by_contra h
    have hrad := dyadicRadius_antitone (le_of_not_gt h)
    have hr := dyadicRadius_pos a
    linarith
  · by_contra h
    have hrad := dyadicRadius_antitone (le_of_not_gt h)
    have h12 : dyadicRadius (12 : ℕ) = 1 / 4096 := by
      norm_num [dyadicRadius, Real.rpow_neg, Real.rpow_natCast]
    rw [dyadicRadius_add, h12] at hrad
    linarith [dyadicRadius_pos p]

end FalconerThetaGauge
