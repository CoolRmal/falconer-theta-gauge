module

public import FalconerThetaGauge.DistanceLinearizationCells

/-! # Actual distance collisions force the projection collisions of source §7.7 -/

@[expose] public section

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem pairDistance_collision_projection_le {a b : Plane} (hab : a ≠ b)
    {x x' y y' : Plane} {η δ : ℝ}
    (hcollision : |‖x - y‖ - ‖x' - y'‖| ≤ η)
    (herror : |pairDistanceLinearizationError a b x y| ≤ δ)
    (herror' : |pairDistanceLinearizationError a b x' y'| ≤ δ) :
    |inner ℝ (pairDirection a b : Plane) (x - x') -
      inner ℝ (pairDirection a b : Plane) (y - y')| ≤ η + 2 * δ := by
  have h₁ := pairDistance_linearization hab x y
  have h₂ := pairDistance_linearization hab x' y'
  have heq : inner ℝ (pairDirection a b : Plane) (x - x') -
      inner ℝ (pairDirection a b : Plane) (y - y') =
      (‖x - y‖ - ‖x' - y'‖) - (pairDistanceLinearizationError a b x y -
        pairDistanceLinearizationError a b x' y') := by
    simp only [inner_sub_right] at h₁ h₂ ⊢
    linarith
  rw [heq]
  calc
    _ ≤ |‖x - y‖ - ‖x' - y'‖| + |pairDistanceLinearizationError a b x y -
        pairDistanceLinearizationError a b x' y'| := abs_sub _ _
    _ ≤ η + (|pairDistanceLinearizationError a b x y| +
        |pairDistanceLinearizationError a b x' y'|) := add_le_add hcollision (abs_sub _ _)
    _ ≤ _ := by linarith

/-- Every actual four-point distance collision in the retained fine-cell pair
satisfies the literal two-projection collision with tolerance `2·2⁻ᵗ`. -/
theorem distance_collision_projection_collision_cells {a p t : ℕ} {A B P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) (hP : dyadicCube p P ⊆ dyadicCube a A)
    (hQ : dyadicCube p Q ⊆ dyadicCube a B) (hdepth : a + t < 2 * p)
    {x x' y y' : Plane} (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P)
    (hy : y ∈ dyadicCube p Q) (hy' : y' ∈ dyadicCube p Q)
    (hcollision : |dist x y - dist x' y'| ≤ (2 : ℝ) ^ (-(t : ℝ))) :
    |inner ℝ (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q) : Plane) (x - x') -
      inner ℝ (pairDirection (dyadicCellCenter p P) (dyadicCellCenter p Q) : Plane) (y - y')| ≤
        2 * (2 : ℝ) ^ (-(t : ℝ)) := by
  have hD := (dist_bounds_of_separatedDyadicCells hsep
    (hP (dyadicCellCenter_mem_dyadicCube p P)) (hQ (dyadicCellCenter_mem_dyadicCube p Q))).1
  have hab : dyadicCellCenter p P ≠ dyadicCellCenter p Q := by
    apply dist_pos.mp
    linarith [dyadicRadius_pos a]
  have h := pairDistance_collision_projection_le hab
    (by simpa only [dist_eq_norm] using hcollision)
    (pairDistanceLinearizationError_cells_le hsep hP hQ hdepth hx hy)
    (pairDistanceLinearizationError_cells_le hsep hP hQ hdepth hx' hy')
  apply h.trans
  linarith [show 0 < (2 : ℝ) ^ (-(t : ℝ)) by positivity]

end FalconerThetaGauge
