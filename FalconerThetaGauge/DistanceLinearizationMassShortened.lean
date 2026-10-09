module

public import FalconerThetaGauge.DistanceLinearizationMassDecomposition

/-! # The actual retained union is carried by the actual shorter passing list -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem retainedFineCellPairCarrier_subset_shortened_passing (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {a p : ℕ} (hap : a ≤ p) {A B : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a A B) {E width width' : ℝ} (hE : 0 ≤ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest} (hJ₁ : J₁ ⊆ I₁) (hJ₂ : J₂ ⊆ I₂)
    (hordered₁ : ScheduledTestsOrdered J₁) (hordered₂ : ScheduledTestsOrdered J₂)
    (hshort₁ : ∀ test ∈ J₁, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hshort₂ : ∀ test ∈ J₂, test.anchor ≤ p ∧ a + test.length ≤ p) :
    fineCellPairCarrier p (retainedFineCellPairs ρ a p A B
        (scheduledPassingPairSet ρ ρ E width I₁ I₂)) ⊆
      scheduledPassingPairSet ρ ρ E width' J₁ J₂ := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := mem_iUnion₂.1 hz
  obtain ⟨hPQ, hwitness⟩ := Finset.mem_filter.1 hR
  obtain ⟨hP, hQ⟩ := Finset.mem_product.1 hPQ
  have hPocc : R.1 ∈ occupiedUnitCells ρ p :=
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hP).1, (Finset.mem_filter.1 hP).2.2⟩
  have hQocc : R.2 ∈ occupiedUnitCells ρ p :=
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hQ).1, (Finset.mem_filter.1 hQ).2.2⟩
  exact retained_cell_pair_subset_shortened_passing ρ hsep
    (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap hP)
    (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap hQ) hPocc hQocc hE hgap
    hJ₁ hJ₂ hordered₁ hordered₂ hshort₁ hshort₂ hwitness hzR

/-- The actual sum of retained fine-cell distance measures is dominated by shorter passing. -/
theorem sum_crossDistanceMeasure_retained_le_shortened (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a p : ℕ} (hap : a ≤ p) {A B : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    {E width width' : ℝ} (hE : 0 ≤ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest} (hJ₁ : J₁ ⊆ I₁) (hJ₂ : J₂ ⊆ I₂)
    (hordered₁ : ScheduledTestsOrdered J₁) (hordered₂ : ScheduledTestsOrdered J₂)
    (hshort₁ : ∀ test ∈ J₁, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hshort₂ : ∀ test ∈ J₂, test.anchor ≤ p ∧ a + test.length ≤ p) :
    Measure.sum (fun R : retainedFineCellPairs ρ a p A B
        (scheduledPassingPairSet ρ ρ E width I₁ I₂) ↦
      crossDistanceMeasure (ρ.restrict (dyadicCube p R.1.1))
        (ρ.restrict (dyadicCube p R.1.2))) ≤
      passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
        (scheduledPassingPairSet ρ ρ E width' J₁ J₂) := by
  rw [← passingUnweightedDistanceMeasure_retained_eq_sum ρ hap]
  apply Measure.map_mono _ continuous_dist.measurable
  exact Measure.restrict_mono_set _
    (retainedFineCellPairCarrier_subset_shortened_passing ρ hap hsep hE hgap
      hJ₁ hJ₂ hordered₁ hordered₂ hshort₁ hshort₂)

end FalconerThetaGauge
