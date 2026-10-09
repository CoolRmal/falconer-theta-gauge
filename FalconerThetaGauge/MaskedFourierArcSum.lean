module

public import FalconerThetaGauge.MaskedFourierArcEnergy
public import FalconerThetaGauge.MaskedFourierActiveCells

/-! # Nonnegative diagonal arc sums over the actual occupied fine cell pairs -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem maskedFourierArcPairEnergy_nonneg (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) (ℓ : ℝ)
    (i j : Fin (angularPartitionCount ℓ)) :
    0 ≤ maskedFourierArcPairEnergy ρ₁ ρ₂ X Y b₁ b₂ K v ℓ i j :=
  integral_nonneg fun _ ↦ sq_nonneg _

theorem sum_active_arc_energy_le_occupied (ρ₁ ρ₂ : Measure Plane) (a p : ℕ)
    (X Y : Fin 2 → ℤ) (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) (ℓ : ℝ)
    (i j : Fin (angularPartitionCount ℓ)) :
    (∑ P ∈ (symbolActiveCellDescendants ρ₁ a p X K ℓ i b₁).product
        (symbolActiveCellDescendants ρ₂ a p Y K ℓ j b₂),
      maskedFourierArcPairEnergy ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2)
        b₁ b₂ K v ℓ i j) ≤
    ∑ P ∈ (occupiedCellDescendants ρ₁ a p X).product (occupiedCellDescendants ρ₂ a p Y),
      maskedFourierArcPairEnergy ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2)
        b₁ b₂ K v ℓ i j := by
  apply sum_le_sum_of_subset_of_nonneg
    (product_subset_product (filter_subset _ _) (filter_subset _ _))
  intro P _ _
  exact maskedFourierArcPairEnergy_nonneg _ _ _ _ _ _ _ _ _ _ _

/-- Summing the true diagonal arc energies recovers every actual fine-cell `F` exactly. -/
theorem sum_occupied_arc_energy_eq (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (a p : ℕ) (X Y : Fin 2 → ℤ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∑ i : Fin (angularPartitionCount ℓ), ∑ j : Fin (angularPartitionCount ℓ),
      ∑ P ∈ (occupiedCellDescendants ρ₁ a p X).product (occupiedCellDescendants ρ₂ a p Y),
        maskedFourierArcPairEnergy ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2)
          b₁ b₂ K v ℓ i j) =
    ∑ P ∈ (occupiedCellDescendants ρ₁ a p X).product (occupiedCellDescendants ρ₂ a p Y),
      (ρ₁.real (dyadicCube p P.1) * ρ₂.real (dyadicCube p P.2)) *
        maskedFourierEnergy ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ K v := by
  have he : ∀ i : Fin (angularPartitionCount ℓ),
      (∑ j : Fin (angularPartitionCount ℓ),
        ∑ P ∈ (occupiedCellDescendants ρ₁ a p X).product (occupiedCellDescendants ρ₂ a p Y),
          maskedFourierArcPairEnergy ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2)
            b₁ b₂ K v ℓ i j) =
      ∑ P ∈ (occupiedCellDescendants ρ₁ a p X).product (occupiedCellDescendants ρ₂ a p Y),
        ∑ j : Fin (angularPartitionCount ℓ),
          maskedFourierArcPairEnergy ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2)
            b₁ b₂ K v ℓ i j := fun _ ↦ sum_comm
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro P _
  exact sum_maskedFourierArcPairEnergy ρ₁ ρ₂ _ _ hb₁ hb₂ hbound₁ hbound₂ K v hℓ

end FalconerThetaGauge
