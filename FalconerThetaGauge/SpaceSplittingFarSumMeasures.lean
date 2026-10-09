/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingDistanceCover
public import FalconerThetaGauge.SpaceSplittingSpatialKernelBounds

/-! # The genuine fine four-point measures sum exactly to the root four-point measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingFineFourMeasure (ρ : Measure Plane) (p : ℕ)
    (P Q : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    Measure ((Plane × Plane) × (Plane × Plane)) :=
  ((ρ.restrict (dyadicCube p P.1)).prod (ρ.restrict (dyadicCube p Q.1))).prod
    ((ρ.restrict (dyadicCube p P.2)).prod (ρ.restrict (dyadicCube p Q.2)))

instance (ρ : Measure Plane) [IsFiniteMeasure ρ] (p : ℕ)
    (P Q : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    IsFiniteMeasure (spaceSplittingFineFourMeasure ρ p P Q) := by
  unfold spaceSplittingFineFourMeasure
  infer_instance

def spaceSplittingFinePairs (ρ : Measure Plane) (a p : ℕ) (X Y : Fin 2 → ℤ) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y)

theorem sum_spaceSplittingFineFourMeasure (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p) (X Y : Fin 2 → ℤ) :
    (∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y, spaceSplittingFineFourMeasure ρ p P Q) =
      spaceSplittingRootFourMeasure ρ a X Y := by
  simp only [spaceSplittingFinePairs, product_eq_sprod, sum_product,
    spaceSplittingFineFourMeasure]
  rw [spaceSplittingRootFourMeasure,
    restrict_dyadicCube_eq_sum_occupiedCellDescendants ρ hρ hap X,
    restrict_dyadicCube_eq_sum_occupiedCellDescendants ρ hρ hap Y]
  simp_rw [prod_finsetSum_measure]

theorem integrable_spaceSplittingFineFourMeasure (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {f : (Plane × Plane) × (Plane × Plane) → ℝ}
    (hf : Integrable f (spaceSplittingRootFourMeasure ρ a X Y))
    {P Q : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hP : P ∈ spaceSplittingFinePairs ρ a p X Y)
    (hQ : Q ∈ spaceSplittingFinePairs ρ a p X Y) :
    Integrable f (spaceSplittingFineFourMeasure ρ p P Q) := by
  rw [← sum_spaceSplittingFineFourMeasure ρ hρ hap X Y,
    integrable_finsetSum_measure] at hf
  exact integrable_finsetSum_measure.1 (hf P hP) Q hQ

theorem sum_integral_spaceSplittingFineFourMeasure (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {f : (Plane × Plane) × (Plane × Plane) → ℝ}
    (hf : Integrable f (spaceSplittingRootFourMeasure ρ a X Y)) :
    (∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
        ∫ z, f z ∂spaceSplittingFineFourMeasure ρ p P Q) =
      ∫ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y := by
  rw [← sum_spaceSplittingFineFourMeasure ρ hρ hap X Y] at hf ⊢
  have hfP := integrable_finsetSum_measure.1 hf
  rw [integral_finsetSum_measure hfP]
  apply sum_congr rfl
  intro P hP
  exact (integral_finsetSum_measure (integrable_finsetSum_measure.1 (hfP P hP))).symm

end FalconerThetaGauge
