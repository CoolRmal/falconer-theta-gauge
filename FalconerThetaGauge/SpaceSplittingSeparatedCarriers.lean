module

public import FalconerThetaGauge.SpaceSplittingCellMeasures
public import FalconerThetaGauge.DistanceLinearizationMassDecomposition
public import FalconerThetaGauge.SpaceSplittingDistanceBins

/-! # Actual finite separated-cell carriers for the source distance bins -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingSeparatedCarrier (ρ : Measure Plane) (a n : ℕ) (X : Fin 2 → ℤ) :
    Set (Plane × Plane) :=
  fineCellPairCarrier n (spaceSplittingSeparatedPairs ρ a n X)

theorem measurableSet_spaceSplittingSeparatedCarrier (ρ : Measure Plane) (a n : ℕ)
    (X : Fin 2 → ℤ) : MeasurableSet (spaceSplittingSeparatedCarrier ρ a n X) :=
  measurableSet_fineCellPairCarrier _ _

theorem spaceSplittingSeparatedCarrier_subset_root (ρ : Measure Plane) {a n : ℕ}
    (han : a ≤ n) (X : Fin 2 → ℤ) :
    spaceSplittingSeparatedCarrier ρ a n X ⊆ dyadicCube a X ×ˢ dyadicCube a X := by
  intro z hz
  obtain ⟨P, hP, hz⟩ := mem_iUnion₂.1 hz
  obtain ⟨hP, _⟩ := mem_filter.1 hP
  obtain ⟨hP₁, hP₂⟩ := mem_product.1 hP
  exact ⟨dyadicCube_subset_of_mem_occupiedCellDescendants ρ han hP₁ hz.1,
    dyadicCube_subset_of_mem_occupiedCellDescendants ρ han hP₂ hz.2⟩

/-- The actual separated carrier restriction is the literal sum of its pair-cell measures. -/
theorem restrict_spaceSplittingSeparatedCarrier_eq_sum (ρ : Measure Plane)
    [SFinite ρ] {a n : ℕ} (han : a ≤ n) (X : Fin 2 → ℤ) :
    ((ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a X))).restrict
        (spaceSplittingSeparatedCarrier ρ a n X) =
      ∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
        (ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2)) := by
  rw [Measure.prod_restrict, Measure.restrict_restrict
    (measurableSet_spaceSplittingSeparatedCarrier ρ a n X),
    inter_eq_left.2 (spaceSplittingSeparatedCarrier_subset_root ρ han X)]
  rw [spaceSplittingSeparatedCarrier, fineCellPairCarrier,
    Measure.restrict_biUnion_finset
      (fun P _ Q _ hPQ ↦ dyadicCellPairs_pairwiseDisjoint n hPQ)
      (fun P ↦ (measurableSet_dyadicCube n P.1).prod (measurableSet_dyadicCube n P.2)),
    Measure.sum_fintype]
  simp only [← Measure.prod_restrict]
  exact sum_attach (spaceSplittingSeparatedPairs ρ a n X)
    (fun P ↦ (ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2)))

theorem lintegral_restrict_spaceSplittingSeparatedCarriers_eq_sum (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {a n : ℕ} (han : a ≤ n) (X Y : Fin 2 → ℤ)
    (f : (Plane × Plane) × (Plane × Plane) → ℝ≥0∞) :
    (∫⁻ z, f z
      ∂(((ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a X))).prod
          ((ρ.restrict (dyadicCube a Y)).prod (ρ.restrict (dyadicCube a Y)))).restrict
        (spaceSplittingSeparatedCarrier ρ a n X ×ˢ spaceSplittingSeparatedCarrier ρ a n Y)) =
      ∑ P ∈ spaceSplittingSeparatedPairs ρ a n X,
        ∑ Q ∈ spaceSplittingSeparatedPairs ρ a n Y,
          ∫⁻ z, f z
            ∂((ρ.restrict (dyadicCube n P.1)).prod (ρ.restrict (dyadicCube n P.2))).prod
              ((ρ.restrict (dyadicCube n Q.1)).prod (ρ.restrict (dyadicCube n Q.2))) := by
  rw [← Measure.prod_restrict,
    restrict_spaceSplittingSeparatedCarrier_eq_sum ρ han X,
    restrict_spaceSplittingSeparatedCarrier_eq_sum ρ han Y,
    lintegral_prod_finsetSum_measure]

end FalconerThetaGauge
