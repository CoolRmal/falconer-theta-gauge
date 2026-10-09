module

public import FalconerThetaGauge.OrthogonalityKernelAngularSource

/-! # A failed true center radial link separates the actual phase on both arcs -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman

theorem orthogonality_radialPhase_gt_half_of_center_failure {a p : ℕ} {E : ℝ}
    (hE : 0 ≤ E) (hlarge : 12 ≤ (2 : ℝ) ^ (E / 2)) (K : ℕ)
    {X Y P P' Q Q' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    (hQ : dyadicCube p Q ⊆ dyadicCube a Y) (hQ' : dyadicCube p Q' ⊆ dyadicCube a Y)
    {x x' y y' : Plane} (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (hy : y ∈ dyadicCube p Q) (hy' : y' ∈ dyadicCube p Q')
    (i j : Fin (angularPartitionCount (orthogonalityArcScale a p E)))
    {w₁ w₂ : UnitCircle}
    (hw₁ : equalArcCutoff K (orthogonalityArcScale a p E) i w₁ ≠ 0)
    (hw₂ : equalArcCutoff K (orthogonalityArcScale a p E) j w₂ ≠ 0)
    (hfail : orthogonalityLinkThreshold p E <
      |inner ℝ (unitCircleOfAngle (equalAngularCellCenter _ i) : Plane)
          (dyadicCellCenter p P - dyadicCellCenter p P') +
        inner ℝ (unitCircleOfAngle (equalAngularCellCenter _ j) : Plane)
          (dyadicCellCenter p Q - dyadicCellCenter p Q')|) :
    orthogonalityLinkThreshold p E / 2 < |orthogonalityRadialPhase x x' y y' w₁ w₂| := by
  have herr₁ := orthogonality_point_center_error hP hP' hx hx' hE K i hw₁
  have herr₂ := orthogonality_point_center_error hQ hQ' hy hy' hE K j hw₂
  have he := orthogonality_phase_error_le_half (p := p) hlarge
  apply abs_gt_half_of_center_failure hfail
  rw [orthogonalityRadialPhase, real_inner_comm (w₁ : Plane) (x - x'),
    real_inner_comm (w₂ : Plane) (y - y')]
  have hh := abs_add_le
    (inner ℝ (w₁ : Plane) (x - x') -
      inner ℝ (angularDirection (equalAngularCellCenter _ i))
        (dyadicCellCenter p P - dyadicCellCenter p P'))
    (inner ℝ (w₂ : Plane) (y - y') -
      inner ℝ (angularDirection (equalAngularCellCenter _ j))
        (dyadicCellCenter p Q - dyadicCellCenter p Q'))
  rw [show ∀ A B C D : ℝ, A - C + (B - D) = (A + B) - (C + D) by intros; ring] at hh
  simp only [coe_unitCircleOfAngle]
  linarith

end FalconerThetaGauge
