module

public import FalconerThetaGauge.OrthogonalityLinks

/-! # An unlinked actual row and column have a separated radial or angular phase -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped InnerProductSpace Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem abs_gt_half_of_center_failure {t c z : ℝ} (hfail : t < |c|)
    (herr : |z - c| ≤ t / 2) : t / 2 < |z| := by
  have hh := abs_sub_abs_le_abs_sub c z
  rw [abs_sub_comm c z] at hh
  linarith

theorem orthogonality_phase_error_le_half {p : ℕ} {E : ℝ}
    (hE : 12 ≤ (2 : ℝ) ^ (E / 2)) :
    6 * dyadicRadius p * (2 : ℝ) ^ E ≤ orthogonalityLinkThreshold p E / 2 := by
  rw [orthogonalityLinkThreshold_eq]
  have hh := mul_le_mul_of_nonneg_left hE
    (mul_nonneg (dyadicRadius_pos p).le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) E).le)
  nlinarith

/-- This is the source's actual pointwise alternative after all center and arc replacements. -/
theorem orthogonality_unlinked_phase_separation {a p : ℕ} {E : ℝ}
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
    (hnot : ¬orthogonalityLinked p (orthogonalityLinkThreshold p E)
      (unitCircleOfAngle (equalAngularCellCenter _ i))
      (unitCircleOfAngle (equalAngularCellCenter _ j)) (P, Q) (P', Q')) :
    orthogonalityLinkThreshold p E / 2 <
        |inner ℝ (circleQuarterTurn w₁ : Plane) (x - x')| ∨
      orthogonalityLinkThreshold p E / 2 <
        |inner ℝ (circleQuarterTurn w₂ : Plane) (y - y')| ∨
      orthogonalityLinkThreshold p E / 2 <
        |inner ℝ (w₁ : Plane) (x - x') + inner ℝ (w₂ : Plane) (y - y')| := by
  let u := unitCircleOfAngle (equalAngularCellCenter
    (angularPartitionCount (orthogonalityArcScale a p E)) i)
  let v := unitCircleOfAngle (equalAngularCellCenter
    (angularPartitionCount (orthogonalityArcScale a p E)) j)
  let τ := orthogonalityLinkThreshold p E
  let e := 3 * dyadicRadius p * (2 : ℝ) ^ E
  have he₀ : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg (mul_nonneg (by norm_num) (dyadicRadius_pos p).le)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) E).le
  have he : 2 * e ≤ τ / 2 := by
    dsimp [e, τ]
    nlinarith [orthogonality_phase_error_le_half (p := p) hlarge]
  have hperp₁ := orthogonality_point_center_perp_error hP hP' hx hx' hE K i hw₁
  have hperp₂ := orthogonality_point_center_perp_error hQ hQ' hy hy' hE K j hw₂
  change ¬orthogonalityLinked p τ u v (P, Q) (P', Q') at hnot
  by_cases h₁ : |inner ℝ (circleQuarterTurn u : Plane)
      (dyadicCellCenter p P - dyadicCellCenter p P')| ≤ τ
  · by_cases h₂ : |inner ℝ (circleQuarterTurn v : Plane)
        (dyadicCellCenter p Q - dyadicCellCenter p Q')| ≤ τ
    · have h₃ : τ < |inner ℝ (u : Plane) (dyadicCellCenter p P - dyadicCellCenter p P') +
          inner ℝ (v : Plane) (dyadicCellCenter p Q - dyadicCellCenter p Q')| :=
        lt_of_not_ge (fun h ↦ hnot ⟨h₁, h₂, h⟩)
      have herr₁ := orthogonality_point_center_error hP hP' hx hx' hE K i hw₁
      have herr₂ := orthogonality_point_center_error hQ hQ' hy hy' hE K j hw₂
      change |inner ℝ (w₁ : Plane) (x - x') -
        inner ℝ (u : Plane) (dyadicCellCenter p P - dyadicCellCenter p P')| ≤ e at herr₁
      change |inner ℝ (w₂ : Plane) (y - y') -
        inner ℝ (v : Plane) (dyadicCellCenter p Q - dyadicCellCenter p Q')| ≤ e at herr₂
      have herr : |(inner ℝ (w₁ : Plane) (x - x') + inner ℝ (w₂ : Plane) (y - y')) -
          (inner ℝ (u : Plane) (dyadicCellCenter p P - dyadicCellCenter p P') +
          inner ℝ (v : Plane) (dyadicCellCenter p Q - dyadicCellCenter p Q'))| ≤ τ / 2 := by
        have hh := abs_add_le
          (inner ℝ (w₁ : Plane) (x - x') -
            inner ℝ (u : Plane) (dyadicCellCenter p P - dyadicCellCenter p P'))
          (inner ℝ (w₂ : Plane) (y - y') -
            inner ℝ (v : Plane) (dyadicCellCenter p Q - dyadicCellCenter p Q'))
        rw [show ∀ A B C D : ℝ, A - C + (B - D) = (A + B) - (C + D) by intros; ring]
          at hh
        linarith
      exact Or.inr (Or.inr (abs_gt_half_of_center_failure h₃ herr))
    · exact Or.inr (Or.inl (abs_gt_half_of_center_failure (lt_of_not_ge h₂)
        (hperp₂.trans (by change e ≤ τ / 2; linarith))))
  · exact Or.inl (abs_gt_half_of_center_failure (lt_of_not_ge h₁)
      (hperp₁.trans (by change e ≤ τ / 2; linarith)))

end FalconerThetaGauge
