module

public import FalconerThetaGauge.SpaceSplittingNearCells
public import FalconerThetaGauge.FiniteGraphSchur
public import FalconerThetaGauge.RegularMeasureExcessCount
public import FalconerThetaGauge.MaskedDistanceEnergyCells

/-! # Literal separated-cell partner counts and their weighted Schur sum -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem separatedDyadicCells_symm {n : ℕ} {P Q : Fin 2 → ℤ}
    (h : SeparatedDyadicCells n P Q) : SeparatedDyadicCells n Q P := by
  simpa only [SeparatedDyadicCells, dist_comm] using h

theorem separatedPartnerIndexBox_card (n : ℕ) (P : Fin 2 → ℤ) :
    (dyadicCenterBallIndexBox n P ((10000 / 3 : ℝ) * dyadicRadius n)).card = 20001 ^ 2 := by
  have heq : 3 * ((10000 / 3 : ℝ) * dyadicRadius n) * (2 : ℝ) ^ n = 10000 := by
    rw [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    field_simp
  rw [card_dyadicCenterBallIndexBox, heq]
  norm_num

theorem separatedDyadicCells_partner_card_le (n : ℕ) (I : Finset (Fin 2 → ℤ))
    (P : Fin 2 → ℤ) : (I.filter (SeparatedDyadicCells n P)).card ≤ 20001 ^ 2 := by
  have hsub : I.filter (SeparatedDyadicCells n P) ⊆
      dyadicCenterBallIndexBox n P ((10000 / 3 : ℝ) * dyadicRadius n) := by
    intro Q hQ
    apply mem_dyadicCenterBallIndexBox
    have h := (mem_filter.1 hQ).2.2
    rw [dist_comm, dist_eq_norm] at h
    convert h using 1
    ring
  exact (Finset.card_le_card hsub).trans_eq (separatedPartnerIndexBox_card n P)

def spaceSplittingSeparatedPairs (ρ : Measure Plane) (a n : ℕ) (X : Fin 2 → ℤ) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  ((occupiedCellDescendants ρ a n X).product (occupiedCellDescendants ρ a n X)).filter
    (fun P ↦ SeparatedDyadicCells n P.1 P.2)

/-- The actual separated partners cost the source's `(20K+1)²` in the root mass sum. -/
theorem sum_sqrt_mass_spaceSplittingSeparatedPairs_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a n : ℕ} (han : a ≤ n) (X : Fin 2 → ℤ) :
    (∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
      Real.sqrt (ρ.real (dyadicCube n P.1) * ρ.real (dyadicCube n P.2))) ≤
        (20001 : ℝ) ^ 2 * ρ.real (dyadicCube a X) := by
  let I := occupiedCellDescendants ρ a n X
  have hdegree : ∀ P ∈ I, ((I.filter (SeparatedDyadicCells n P)).card : ℝ) ≤
      (20001 : ℝ) ^ 2 := by
    intro P _
    exact_mod_cast separatedDyadicCells_partner_card_le n I P
  have hh := finite_graph_schur I (SeparatedDyadicCells n)
    (fun {_ _} h ↦ separatedDyadicCells_symm h)
    (fun P ↦ Real.sqrt (ρ.real (dyadicCube n P))) hdegree
  simp only [Real.sq_sqrt measureReal_nonneg] at hh
  calc
    _ = ∑ P ∈ I, ∑ Q ∈ I,
        if SeparatedDyadicCells n P Q then
          Real.sqrt (ρ.real (dyadicCube n P)) * Real.sqrt (ρ.real (dyadicCube n Q))
        else 0 := by
      unfold spaceSplittingSeparatedPairs
      rw [sum_filter, product_eq_sprod, sum_product]
      apply sum_congr rfl
      intro P _
      apply sum_congr rfl
      intro Q _
      split_ifs
      · exact Real.sqrt_mul measureReal_nonneg _
      · rfl
    _ ≤ (20001 : ℝ) ^ 2 * ∑ P ∈ I, ρ.real (dyadicCube n P) := hh
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_occupiedCellDescendants_le ρ han X)
      (by positivity)

def spaceSplittingRegroupingConstant : ℝ := 10 * (2 : ℝ) ^ (25 : ℕ) * 20001 ^ (4 : ℕ)

theorem spaceSplittingRegroupingConstant_le_source :
    spaceSplittingRegroupingConstant ≤ (2 : ℝ) ^ (90 : ℕ) := by
  norm_num [spaceSplittingRegroupingConstant]

end FalconerThetaGauge
