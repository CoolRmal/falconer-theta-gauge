module

public import FalconerThetaGauge.OrthogonalityGridCount

/-! # The actual linked second-cell fiber has a uniformly bounded lattice count -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

theorem norm_second_centers_sub_le_of_linked {p : ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    {w₁ w₂ : UnitCircle} {row : (Fin 2 → ℤ) × (Fin 2 → ℤ)} {P' Q₁ Q₂ : Fin 2 → ℤ}
    (h₁ : orthogonalityLinked p τ w₁ w₂ row (P', Q₁))
    (h₂ : orthogonalityLinked p τ w₁ w₂ row (P', Q₂)) :
    ‖dyadicCellCenter p Q₁ - dyadicCellCenter p Q₂‖ ≤ 3 * τ := by
  apply norm_le_three_of_two_coordinates (w := w₂) hτ
  · let A := inner ℝ (w₁ : Plane) (dyadicCellCenter p row.1 - dyadicCellCenter p P')
    let B₁ := inner ℝ (w₂ : Plane) (dyadicCellCenter p row.2 - dyadicCellCenter p Q₁)
    let B₂ := inner ℝ (w₂ : Plane) (dyadicCellCenter p row.2 - dyadicCellCenter p Q₂)
    have hh := abs_add_le (A + B₂) (-(A + B₁))
    rw [abs_neg, ← sub_eq_add_neg] at hh
    have he : inner ℝ (w₂ : Plane) (dyadicCellCenter p Q₁ - dyadicCellCenter p Q₂) =
        (A + B₂) - (A + B₁) := by
      dsimp [A, B₁, B₂]
      simp only [inner_sub_right]
      ring
    rw [he]
    have hb₁ : |A + B₁| ≤ τ := h₁.2.2
    have hb₂ : |A + B₂| ≤ τ := h₂.2.2
    linarith
  · have hh := abs_add_le
      (inner ℝ (circleQuarterTurn w₂ : Plane)
        (dyadicCellCenter p row.2 - dyadicCellCenter p Q₂))
      (-inner ℝ (circleQuarterTurn w₂ : Plane)
        (dyadicCellCenter p row.2 - dyadicCellCenter p Q₁))
    rw [abs_neg, ← sub_eq_add_neg] at hh
    have he : inner ℝ (circleQuarterTurn w₂ : Plane)
        (dyadicCellCenter p Q₁ - dyadicCellCenter p Q₂) =
        inner ℝ (circleQuarterTurn w₂ : Plane)
          (dyadicCellCenter p row.2 - dyadicCellCenter p Q₂) -
        inner ℝ (circleQuarterTurn w₂ : Plane)
          (dyadicCellCenter p row.2 - dyadicCellCenter p Q₁) := by
      simp only [inner_sub_right]
      ring
    rw [he]
    linarith [h₁.2.1, h₂.2.1]

def linkedSecondColumns (ρ : Measure Plane) (p : ℕ) (τ : ℝ) (w₁ w₂ : UnitCircle)
    (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) (P' : Fin 2 → ℤ) : Finset (Fin 2 → ℤ) :=
  (occupiedUnitCells ρ p).filter (fun Q' ↦ orthogonalityLinked p τ w₁ w₂ row (P', Q'))

theorem linkedSecondColumns_count_le (ρ : Measure Plane) (p : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (w₁ w₂ : UnitCircle) (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) (P' : Fin 2 → ℤ) :
    ((linkedSecondColumns ρ p (orthogonalityLinkThreshold p E) w₁ w₂ row P').card : ℝ) ≤
      81 * (2 : ℝ) ^ (3 * E) := by
  let S := linkedSecondColumns ρ p (orthogonalityLinkThreshold p E) w₁ w₂ row P'
  by_cases hS : S.Nonempty
  · obtain ⟨Q₀, hQ₀⟩ := hS
    apply finite_dyadic_link_count_le hE S Q₀
    intro Q hQ
    apply norm_second_centers_sub_le_of_linked ?_ (mem_filter.mp hQ).2 (mem_filter.mp hQ₀).2
    unfold orthogonalityLinkThreshold
    exact mul_nonneg (GaugeFrostman.dyadicRadius_pos p).le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

end FalconerThetaGauge
