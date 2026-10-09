/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsPiecesPadding

/-! # Assembly across disjoint finite piece carriers -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace FalconerThetaGauge

def pieceFilterCarrier {ι : Type*} {N : ℕ} {E : ℝ} (I : Finset ι)
    (F : ι → FiniteDirectionalFilter N E) : Set Plane := ⋃ t ∈ I, (F t).carrier

def pieceFilterBadTest {ι : Type*} {N : ℕ} {E : ℝ} (I : Finset ι)
    (F : ι → FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) : Set (Plane × UnitCircle) :=
  ⋃ t ∈ I, (Prod.fst ⁻¹' (F t).carrier) ∩ (F t).paddedBadTest j

def pieceFilterMaskTest {ι : Type*} {N : ℕ} {E : ℝ} (I : Finset ι)
    (F : ι → FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1))
    (x : Plane) (w : UnitCircle) : ℝ :=
  ∑ t ∈ I, (F t).carrier.indicator (fun z => (F t).paddedMaskTest j z w) x

theorem pieceFilterMaskTest_eq_on_piece {ι : Type*} {N : ℕ} {E : ℝ} {I : Finset ι}
    {F : ι → FiniteDirectionalFilter N E}
    (hdisjoint : (I : Set ι).PairwiseDisjoint (fun t => (F t).carrier))
    (j : Fin (N ^ 2 + 1)) {t : ι} (ht : t ∈ I) {x : Plane} (hx : x ∈ (F t).carrier)
    (w : UnitCircle) : pieceFilterMaskTest I F j x w = (F t).paddedMaskTest j x w := by
  rw [pieceFilterMaskTest, sum_eq_single t, indicator_of_mem hx]
  · intro u hu hut
    apply indicator_of_notMem
    intro hxu
    exact hut ((Set.pairwiseDisjoint_iff.mp hdisjoint) hu ht ⟨x, hxu, hx⟩)
  · intro h
    exact False.elim (h ht)

theorem pieceFilterMaskTest_eq_zero_off_pieces {ι : Type*} {N : ℕ} {E : ℝ} (I : Finset ι)
    (F : ι → FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) {x : Plane}
    (hx : ∀ t ∈ I, x ∉ (F t).carrier) (w : UnitCircle) :
    pieceFilterMaskTest I F j x w = 0 := by
  apply sum_eq_zero
  intro t ht
  exact indicator_of_notMem (hx t ht) _

theorem measurable_pieceFilterMaskTest {ι : Type*} {N : ℕ} {E : ℝ} (I : Finset ι)
    (F : ι → FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) :
    Measurable (Function.uncurry (pieceFilterMaskTest I F j)) := by
  change Measurable (fun p : Plane × UnitCircle =>
    ∑ t ∈ I, (F t).carrier.indicator (fun z => (F t).paddedMaskTest j z p.2) p.1)
  apply I.measurable_sum
  intro t _
  have heq : (fun p : Plane × UnitCircle =>
      (F t).carrier.indicator (fun z => (F t).paddedMaskTest j z p.2) p.1) =
      (Prod.fst ⁻¹' (F t).carrier).indicator (Function.uncurry ((F t).paddedMaskTest j)) := by
    ext p
    by_cases hp : p.1 ∈ (F t).carrier <;> simp [hp, Function.uncurry]
  rw [heq]
  exact ((F t).paddedMaskTest_measurable j).indicator
    ((F t).carrier_measurable.preimage measurable_fst)

theorem pieceFilterMaskTest_range {ι : Type*} {N : ℕ} {E : ℝ} {I : Finset ι}
    {F : ι → FiniteDirectionalFilter N E}
    (hdisjoint : (I : Set ι).PairwiseDisjoint (fun t => (F t).carrier))
    (j : Fin (N ^ 2 + 1)) (x : Plane) (w : UnitCircle) :
    pieceFilterMaskTest I F j x w ∈ Set.Icc 0 1 := by
  by_cases hx : ∃ t ∈ I, x ∈ (F t).carrier
  · obtain ⟨t, ht, hxt⟩ := hx
    rw [pieceFilterMaskTest_eq_on_piece hdisjoint j ht hxt]
    exact (F t).paddedMaskTest_range j x w
  · rw [pieceFilterMaskTest_eq_zero_off_pieces I F j
      (by simpa only [not_exists, not_and] using hx)]
    simp

theorem pieceFilterBadTest_section_on_piece {ι : Type*} {N : ℕ} {E : ℝ} {I : Finset ι}
    {F : ι → FiniteDirectionalFilter N E}
    (hdisjoint : (I : Set ι).PairwiseDisjoint (fun t => (F t).carrier))
    (j : Fin (N ^ 2 + 1)) {t : ι} (ht : t ∈ I) {x : Plane} (hx : x ∈ (F t).carrier) :
    badDirectionsAt (pieceFilterBadTest I F j) x = badDirectionsAt ((F t).paddedBadTest j) x := by
  ext w
  change (x, w) ∈ pieceFilterBadTest I F j ↔ (x, w) ∈ (F t).paddedBadTest j
  simp only [pieceFilterBadTest, mem_iUnion, exists_prop, mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨u, hu, hxu, hw⟩
    have hut : u = t := (Set.pairwiseDisjoint_iff.mp hdisjoint) hu ht ⟨x, hxu, hx⟩
    simpa only [hut] using hw
  · intro hw
    exact ⟨t, ht, hx, hw⟩

theorem pieceFilterBadTest_section_off_pieces {ι : Type*} {N : ℕ} {E : ℝ} (I : Finset ι)
    (F : ι → FiniteDirectionalFilter N E) (j : Fin (N ^ 2 + 1)) {x : Plane}
    (hx : ∀ t ∈ I, x ∉ (F t).carrier) : badDirectionsAt (pieceFilterBadTest I F j) x = ∅ := by
  ext w
  change (x, w) ∈ pieceFilterBadTest I F j ↔ w ∈ (∅ : Set UnitCircle)
  simp only [pieceFilterBadTest, mem_iUnion, exists_prop, mem_inter_iff, Set.mem_preimage,
    mem_empty_iff_false, iff_false]
  rintro ⟨t, ht, hxt, _⟩
  exact hx t ht hxt

/-- The slot count depends on the tests per pin, independently of the number of pieces. -/
def assembleDirectionalFilters {ι : Type*} {N : ℕ} {E : ℝ} (I : Finset ι)
    (F : ι → FiniteDirectionalFilter N E)
    (hdisjoint : (I : Set ι).PairwiseDisjoint (fun t => (F t).carrier)) :
    FiniteDirectionalFilter N E where
  carrier := pieceFilterCarrier I F
  carrier_measurable :=
    MeasurableSet.biUnion I.countable_toSet (fun t _ => (F t).carrier_measurable)
  testCount := N ^ 2 + 1
  testCount_le := le_refl _
  badTest := pieceFilterBadTest I F
  badTest_measurable j := MeasurableSet.biUnion I.countable_toSet (fun t _ =>
    ((F t).carrier_measurable.preimage measurable_fst).inter ((F t).paddedBadTest_measurable j))
  badTest_symmetric j x w := by
    simp only [pieceFilterBadTest, mem_iUnion, exists_prop, mem_inter_iff, Set.mem_preimage,
      (F _).paddedBadTest_symmetric j x w]
  badTest_short j x := by
    by_cases hx : ∃ t ∈ I, x ∈ (F t).carrier
    · obtain ⟨t, ht, hxt⟩ := hx
      rw [pieceFilterBadTest_section_on_piece hdisjoint j ht hxt]
      exact (F t).paddedBadTest_short j x
    · rw [pieceFilterBadTest_section_off_pieces I F j
        (by simpa only [not_exists, not_and] using hx), measure_empty]
      exact bot_le
  maskTest := pieceFilterMaskTest I F
  maskTest_measurable := measurable_pieceFilterMaskTest I F
  maskTest_range := pieceFilterMaskTest_range hdisjoint
  maskTest_passing j x hx w hw := by
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    rw [pieceFilterMaskTest_eq_on_piece hdisjoint j ht hxt]
    apply (F t).paddedMaskTest_passing j hxt
    intro hbad
    apply hw
    exact mem_iUnion₂.mpr ⟨t, ht, hxt, hbad⟩

/-- On a retained carrier the assembled product is exactly that piece's original product. -/
theorem assembleDirectionalFilters_symbol_on_piece {ι : Type*} {N : ℕ} {E : ℝ}
    {I : Finset ι} {F : ι → FiniteDirectionalFilter N E}
    (hdisjoint : (I : Set ι).PairwiseDisjoint (fun t => (F t).carrier))
    {t : ι} (ht : t ∈ I) {x : Plane} (hx : x ∈ (F t).carrier) (w : UnitCircle) :
    (assembleDirectionalFilters I F hdisjoint).symbol x w = (F t).symbol x w := by
  have hxI : x ∈ pieceFilterCarrier I F := mem_iUnion₂.mpr ⟨t, ht, hx⟩
  change (if x ∈ pieceFilterCarrier I F then ∏ j, pieceFilterMaskTest I F j x w else 0) =
    (if x ∈ (F t).carrier then ∏ i, (F t).maskTest i x w else 0)
  rw [ite_eq_left hxI, ite_eq_left hx]
  simp_rw [pieceFilterMaskTest_eq_on_piece hdisjoint _ ht hx]
  exact (F t).prod_paddedMaskTest x w

end FalconerThetaGauge
