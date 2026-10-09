module

public import FalconerThetaGauge.SpaceSplittingRegrouping
public import FalconerThetaGauge.MaskedFourierCells

/-! # Exact occupied-descendant decomposition of the actual spatial measures -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem restrict_cellUnion_eq_sum (ρ : Measure Plane) (p : ℕ)
    (I : Finset (Fin 2 → ℤ)) :
    ρ.restrict (cellUnion p I) = ∑ P ∈ I, ρ.restrict (dyadicCube p P) := by
  rw [cellUnion, Measure.restrict_biUnion_finset
    (fun P _ Q _ hPQ ↦ dyadicCube_disjoint hPQ) (measurableSet_dyadicCube p),
    Measure.sum_fintype]
  exact sum_attach I (fun P ↦ ρ.restrict (dyadicCube p P))

/-- The literal root restriction is exactly the sum of its positive occupied descendants. -/
theorem restrict_dyadicCube_eq_sum_occupiedCellDescendants (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X : Fin 2 → ℤ) :
    ρ.restrict (dyadicCube a X) =
      ∑ P ∈ occupiedCellDescendants ρ a p X, ρ.restrict (dyadicCube p P) := by
  have hρU : ρ.restrict unitSquare = ρ := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_mem_iff_measure_eq measurableSet_unitSquare.nullMeasurableSet).mpr
      (by simpa only [measure_univ] using hρ)
  have hre : ρ.restrict (dyadicCube a X ∩ unitSquare) = ρ.restrict (dyadicCube a X) := by
    rw [← Measure.restrict_restrict (measurableSet_dyadicCube a X), hρU]
  let S := (unitCellIndices p).filter (fun P ↦ ancestor (p - a) P = X)
  have hO : occupiedCellDescendants ρ a p X ⊆ S := by
    intro P hP
    obtain ⟨hP, hanc, _⟩ := mem_filter.mp hP
    exact mem_filter.mpr ⟨hP, hanc⟩
  calc
    _ = ρ.restrict (dyadicCube a X ∩ unitSquare) := hre.symm
    _ = ρ.restrict (cellUnion p S) := by
      rw [← biUnion_unitCellIndices p]
      change ρ.restrict (dyadicCube a X ∩ cellUnion p (unitCellIndices p)) = _
      rw [dyadicCube_inter_cellUnion hap]
    _ = ∑ P ∈ S, ρ.restrict (dyadicCube p P) := restrict_cellUnion_eq_sum ρ p S
    _ = _ := by
      symm
      apply sum_subset hO
      intro P hPS hPO
      have hmass : ρ.real (dyadicCube p P) = 0 := by
        have hP := mem_filter.mp hPS
        have hh : ¬0 < unitCellWeight ρ p P := by
          intro hh
          exact hPO (mem_filter.mpr ⟨hP.1, hP.2, hh⟩)
        exact le_antisymm (le_of_not_gt hh) (unitCellWeight_nonneg ρ p P)
      apply Measure.restrict_eq_zero.2
      exact (ENNReal.toReal_eq_zero_iff _).1 hmass |>.resolve_right (measure_ne_top ρ _)

theorem prod_finsetSum_measure {α β ι κ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (I : Finset ι) (J : Finset κ) (μ : ι → Measure α) (ν : κ → Measure β)
    [∀ j, SFinite (ν j)] :
    (∑ i ∈ I, μ i).prod (∑ j ∈ J, ν j) =
      ∑ i ∈ I, ∑ j ∈ J, (μ i).prod (ν j) := by
  rw [← sum_attach I μ, ← sum_attach J ν]
  simp only [attach_eq_univ]
  rw [← Measure.sum_fintype, ← Measure.sum_fintype, Measure.prod_sum,
    Measure.sum_fintype, Fintype.sum_prod_type]
  simp only [← attach_eq_univ]
  calc
    _ = ∑ x ∈ I.attach, ∑ j ∈ J, (μ x).prod (ν j) := by
      apply sum_congr rfl
      intro x _
      exact sum_attach J (fun j ↦ (μ x).prod (ν j))
    _ = _ := sum_attach I (fun i ↦ ∑ j ∈ J, (μ i).prod (ν j))

/-- The genuine root pair measure decomposes over the actual occupied descendant pairs. -/
theorem prod_restrict_dyadicCube_eq_sum_occupiedCellDescendants (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) :
    (ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a Y)) =
      ∑ P ∈ occupiedCellDescendants ρ a p X,
        ∑ Q ∈ occupiedCellDescendants ρ a p Y,
          (ρ.restrict (dyadicCube p P)).prod (ρ.restrict (dyadicCube p Q)) := by
  rw [restrict_dyadicCube_eq_sum_occupiedCellDescendants ρ hρ hap X,
    restrict_dyadicCube_eq_sum_occupiedCellDescendants ρ hρ hap Y,
    prod_finsetSum_measure]

theorem lintegral_prod_finsetSum_measure {α β ι κ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (I : Finset ι) (J : Finset κ) (μ : ι → Measure α) (ν : κ → Measure β)
    [∀ j, SFinite (ν j)] (f : α × β → ℝ≥0∞) :
    (∫⁻ z, f z ∂(∑ i ∈ I, μ i).prod (∑ j ∈ J, ν j)) =
      ∑ i ∈ I, ∑ j ∈ J, ∫⁻ z, f z ∂(μ i).prod (ν j) := by
  rw [prod_finsetSum_measure]
  simp only [lintegral_finsetSum_measure]

theorem ae_mem_cellUnion_occupiedCellDescendants (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X : Fin 2 → ℤ) :
    ∀ᵐ x ∂ρ.restrict (dyadicCube a X),
      x ∈ cellUnion p (occupiedCellDescendants ρ a p X) := by
  have heq : ρ.restrict (dyadicCube a X) =
      ρ.restrict (cellUnion p (occupiedCellDescendants ρ a p X)) := by
    rw [restrict_cellUnion_eq_sum,
      restrict_dyadicCube_eq_sum_occupiedCellDescendants ρ hρ hap X]
  rw [heq]
  exact ae_restrict_mem (measurableSet_cellUnion _ _)

end FalconerThetaGauge
