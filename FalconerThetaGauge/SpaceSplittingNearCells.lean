module

public import FalconerThetaGauge.OrthogonalityGridCount

/-! # Exact near-row lattice count in source Estimate 7.8 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem dyadicCenterBallIndexBox_four_radius_card (p : ℕ) (P : Fin 2 → ℤ) :
    (dyadicCenterBallIndexBox p P ((4 / 3 : ℝ) * dyadicRadius p)).card = 81 := by
  have heq : 3 * ((4 / 3 : ℝ) * dyadicRadius p) * (2 : ℝ) ^ p = 4 := by
    rw [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    field_simp
  rw [card_dyadicCenterBallIndexBox, heq]
  norm_num

/-- The near relation uses precisely the two source center-distance inequalities. -/
def spaceSplittingNear (p : ℕ) (R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : Prop :=
  dist (dyadicCellCenter p R.1) (dyadicCellCenter p S.1) ≤ 4 * dyadicRadius p ∧
    dist (dyadicCellCenter p R.2) (dyadicCellCenter p S.2) ≤ 4 * dyadicRadius p

theorem spaceSplittingNear_symm {p : ℕ} {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (h : spaceSplittingNear p R S) : spaceSplittingNear p S R := by
  simpa only [spaceSplittingNear, dist_comm] using h

theorem spaceSplittingNear_mem_indexBoxes {p : ℕ} {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (h : spaceSplittingNear p R S) :
    S ∈ (dyadicCenterBallIndexBox p R.1 ((4 / 3 : ℝ) * dyadicRadius p)).product
      (dyadicCenterBallIndexBox p R.2 ((4 / 3 : ℝ) * dyadicRadius p)) := by
  apply Finset.mem_product.2
  constructor
  · apply mem_dyadicCenterBallIndexBox
    have h₁ := h.1
    rw [dist_comm, dist_eq_norm] at h₁
    convert h₁ using 1
    ring
  · apply mem_dyadicCenterBallIndexBox
    have h₂ := h.2
    rw [dist_comm, dist_eq_norm] at h₂
    convert h₂ using 1
    ring

/-- Every literal near row has at most `81²` columns, with no measure or support assumption. -/
theorem spaceSplittingNear_row_card_le (p : ℕ)
    (I : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (R : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    (I.filter (spaceSplittingNear p R)).card ≤ 81 ^ (2 : ℕ) := by
  have hsub : I.filter (spaceSplittingNear p R) ⊆
      (dyadicCenterBallIndexBox p R.1 ((4 / 3 : ℝ) * dyadicRadius p)).product
        (dyadicCenterBallIndexBox p R.2 ((4 / 3 : ℝ) * dyadicRadius p)) :=
    fun S hS ↦ spaceSplittingNear_mem_indexBoxes (Finset.mem_filter.1 hS).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.product_eq_sprod, Finset.card_product, dyadicCenterBallIndexBox_four_radius_card,
    dyadicCenterBallIndexBox_four_radius_card] at hcard
  simpa only [pow_two] using hcard

theorem spaceSplittingNear_column_card_le (p : ℕ)
    (I : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (S : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    (I.filter (fun R ↦ spaceSplittingNear p R S)).card ≤ 81 ^ (2 : ℕ) := by
  have heq : I.filter (fun R ↦ spaceSplittingNear p R S) =
      I.filter (spaceSplittingNear p S) := by
    apply Finset.filter_congr
    intro R _
    exact ⟨spaceSplittingNear_symm, spaceSplittingNear_symm⟩
  rw [heq]
  exact spaceSplittingNear_row_card_le p I S

end FalconerThetaGauge
