module

public import FalconerThetaGauge.DistanceLinearizationMassEnergy
public import FalconerThetaGauge.DistanceLinearizationRetained

/-! # Actual finite retained cell pairs and their unweighted distance measure decomposition -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def fineCellPairCarrier (p : ℕ) (I : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    Set (Plane × Plane) :=
  ⋃ R ∈ I, dyadicCube p R.1 ×ˢ dyadicCube p R.2

theorem measurableSet_fineCellPairCarrier (p : ℕ)
    (I : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) : MeasurableSet (fineCellPairCarrier p I) := by
  unfold fineCellPairCarrier
  exact Finset.measurableSet_biUnion I (fun R _ ↦
    (measurableSet_dyadicCube p R.1).prod (measurableSet_dyadicCube p R.2))

theorem dyadicCellPairs_pairwiseDisjoint (p : ℕ) :
    Pairwise (Disjoint on fun R : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
      dyadicCube p R.1 ×ˢ dyadicCube p R.2) := by
  intro R S hRS
  apply Set.disjoint_left.2
  rintro z ⟨hx, hy⟩ ⟨hx', hy'⟩
  apply hRS
  exact Prod.ext ((mem_dyadicCube_iff.1 hx).symm.trans (mem_dyadicCube_iff.1 hx'))
    ((mem_dyadicCube_iff.1 hy).symm.trans (mem_dyadicCube_iff.1 hy'))

/-- The finite retained union's distance measure is exactly the sum of its actual cell measures. -/
theorem map_distance_restrict_fineCellPairCarrier (ρ : Measure Plane) [SFinite ρ]
    (p : ℕ) (I : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    ((ρ.prod ρ).restrict (fineCellPairCarrier p I)).map
        (fun z : Plane × Plane ↦ dist z.1 z.2) =
      Measure.sum (fun R : I ↦
        crossDistanceMeasure (ρ.restrict (dyadicCube p R.1.1))
          (ρ.restrict (dyadicCube p R.1.2))) := by
  rw [fineCellPairCarrier, Measure.restrict_biUnion_finset
    (fun R _ S _ hRS ↦ dyadicCellPairs_pairwiseDisjoint p hRS)
    (fun R ↦ (measurableSet_dyadicCube p R.1).prod (measurableSet_dyadicCube p R.2)),
    Measure.map_sum continuous_dist.measurable.aemeasurable]
  congr 1
  funext R
  rw [crossDistanceMeasure, Measure.prod_restrict]

/-- Every retained pair is genuinely occupied, lies in its coarse carriers, and has a witness. -/
def retainedFineCellPairs (ρ : Measure Plane) (a p : ℕ) (A B : Fin 2 → ℤ)
    (Z : Set (Plane × Plane)) : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  ((occupiedCellDescendants ρ a p A).product (occupiedCellDescendants ρ a p B)).filter
    (fun R ↦ ((dyadicCube p R.1 ×ˢ dyadicCube p R.2) ∩ Z).Nonempty)

theorem dyadicCube_subset_of_mem_occupiedCellDescendants (ρ : Measure Plane) {a p : ℕ}
    (hap : a ≤ p) {A P : Fin 2 → ℤ} (hP : P ∈ occupiedCellDescendants ρ a p A) :
    dyadicCube p P ⊆ dyadicCube a A := by
  have heq := (Finset.mem_filter.1 hP).2.1
  rw [← heq]
  have h := dyadicCube_subset_ancestor a (p - a) P
  simpa only [Nat.add_sub_of_le hap] using h

theorem retainedFineCellPairs_subset_coarse (ρ : Measure Plane) {a p : ℕ} (hap : a ≤ p)
    (A B : Fin 2 → ℤ) (Z : Set (Plane × Plane)) :
    fineCellPairCarrier p (retainedFineCellPairs ρ a p A B Z) ⊆
      dyadicCube a A ×ˢ dyadicCube a B := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := mem_iUnion₂.1 hz
  obtain ⟨hPQ, _⟩ := Finset.mem_filter.1 hR
  obtain ⟨hP, hQ⟩ := Finset.mem_product.1 hPQ
  exact ⟨dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap hP hzR.1,
    dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap hQ hzR.2⟩

theorem passingUnweightedDistanceMeasure_retained_eq_sum (ρ : Measure Plane) [SFinite ρ]
    {a p : ℕ} (hap : a ≤ p) (A B : Fin 2 → ℤ) (Z : Set (Plane × Plane)) :
    passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
        (fineCellPairCarrier p (retainedFineCellPairs ρ a p A B Z)) =
      Measure.sum (fun R : retainedFineCellPairs ρ a p A B Z ↦
        crossDistanceMeasure (ρ.restrict (dyadicCube p R.1.1))
          (ρ.restrict (dyadicCube p R.1.2))) := by
  rw [passingUnweightedDistanceMeasure, Measure.prod_restrict,
    Measure.restrict_restrict (measurableSet_fineCellPairCarrier _ _),
    inter_eq_left.2 (retainedFineCellPairs_subset_coarse ρ hap A B Z),
    map_distance_restrict_fineCellPairCarrier]

/-- Every actual passing pair belongs to a retained fine-cell pair almost everywhere. -/
theorem ae_passing_pair_mem_retained_carrier (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p) (A B : Fin 2 → ℤ)
    (Z : Set (Plane × Plane)) :
    ∀ᵐ z ∂(ρ.restrict (dyadicCube a A)).prod (ρ.restrict (dyadicCube a B)),
      z ∈ Z → z ∈ fineCellPairCarrier p (retainedFineCellPairs ρ a p A B Z) := by
  have hocc : ∀ᵐ x ∂ρ, x ∈ cellUnion p (occupiedUnitCells ρ p) :=
    (ae_mem_iff_measure_eq (measurableSet_cellUnion _ _).nullMeasurableSet).2
      (by simp [measure_cellUnion_occupiedUnitCells ρ hρ])
  have hxocc := (Measure.quasiMeasurePreserving_fst
    (μ := ρ.restrict (dyadicCube a A)) (ν := ρ.restrict (dyadicCube a B))).ae
      (ae_restrict_of_ae hocc)
  have hyocc := (Measure.quasiMeasurePreserving_snd
    (μ := ρ.restrict (dyadicCube a A)) (ν := ρ.restrict (dyadicCube a B))).ae
      (ae_restrict_of_ae hocc)
  filter_upwards [hxocc, hyocc, ae_restricted_product_carriers ρ ρ
    (measurableSet_dyadicCube a A) (measurableSet_dyadicCube a B)] with z hx hy hz
  intro hZ
  obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.1 hx
  obtain ⟨Q, hQ, hyQ⟩ := mem_iUnion₂.1 hy
  have hancestor {P A : Fin 2 → ℤ} {x : Plane}
      (hxP : x ∈ dyadicCube p P) (hxA : x ∈ dyadicCube a A) :
      ancestor (p - a) P = A :=
    (mem_dyadicCube_iff.1 (mem_dyadicCube_ancestor_of_mem hap hxP)).symm.trans
      (mem_dyadicCube_iff.1 hxA)
  have hPdesc : P ∈ occupiedCellDescendants ρ a p A :=
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hP).1,
      hancestor hxP hz.1, (Finset.mem_filter.1 hP).2⟩
  have hQdesc : Q ∈ occupiedCellDescendants ρ a p B :=
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hQ).1,
      hancestor hyQ hz.2, (Finset.mem_filter.1 hQ).2⟩
  exact mem_iUnion₂.2 ⟨(P, Q),
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hPdesc, hQdesc⟩, ⟨z, ⟨hxP, hyQ⟩, hZ⟩⟩,
    ⟨hxP, hyQ⟩⟩

/-- The fine-cell union genuinely dominates the original passing distance measure. -/
theorem passingUnweightedDistanceMeasure_le_retained (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (A B : Fin 2 → ℤ) (Z : Set (Plane × Plane)) :
    passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B) Z ≤
      passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B)
        (fineCellPairCarrier p (retainedFineCellPairs ρ a p A B Z)) := by
  apply Measure.map_mono _ continuous_dist.measurable
  exact Measure.restrict_mono_ae (ae_passing_pair_mem_retained_carrier ρ hρ hap A B Z)

end FalconerThetaGauge
