module

public import FalconerThetaGauge.FilteredDistanceMeasureLoss

/-!
# Finite lists of actual directional tests

These are the literal finite unions and finite products used by Definition
6.12. Each test has a Borel failure set and a Borel `[0,1]` mask. The union
length is deduced from the list cardinality and the individual test lengths.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- The literal union of the failure sets in a finite test list. -/
def finiteBadDirections {ι : Type*} (I : Finset ι) (Z : ι → Set (Plane × UnitCircle)) :
    Set (Plane × UnitCircle) := ⋃ i ∈ I, Z i

theorem measurableSet_finiteBadDirections {ι : Type*} {I : Finset ι}
    {Z : ι → Set (Plane × UnitCircle)} (hZ : ∀ i ∈ I, MeasurableSet (Z i)) :
    MeasurableSet (finiteBadDirections I Z) :=
  MeasurableSet.biUnion I.countable_toSet hZ

theorem isSymmetricBadDirections_finiteBadDirections {ι : Type*} {I : Finset ι}
    {Z : ι → Set (Plane × UnitCircle)} (hZ : ∀ i ∈ I, IsSymmetricBadDirections (Z i)) :
    IsSymmetricBadDirections (finiteBadDirections I Z) := by
  intro x w
  simp only [finiteBadDirections, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, hi, hw⟩
    exact ⟨i, hi, (hZ i hi x w).1 hw⟩
  · rintro ⟨i, hi, hw⟩
    exact ⟨i, hi, (hZ i hi x w).2 hw⟩

/-- The precise `2π(N²+1)2^(-2E)` arc bound follows from the finite list. -/
theorem circleArcLength_finiteBadDirections_le {ι : Type*} (I : Finset ι)
    (Z : ι → Set (Plane × UnitCircle)) (N : ℕ) (E : ℝ)
    (hcard : I.card ≤ N ^ 2 + 1) (x : Plane)
    (hlength : ∀ i ∈ I, circleArcLength (badDirectionsAt (Z i) x) ≤
      ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E))) :
    circleArcLength (badDirectionsAt (finiteBadDirections I Z) x) ≤
      ENNReal.ofReal (filterBadDirectionLength N E) := by
  have heq : badDirectionsAt (finiteBadDirections I Z) x =
      ⋃ i ∈ I, badDirectionsAt (Z i) x := by
    ext w
    simp [badDirectionsAt, finiteBadDirections]
  rw [heq]
  calc
    circleArcLength (⋃ i ∈ I, badDirectionsAt (Z i) x) ≤
        ∑ i ∈ I, circleArcLength (badDirectionsAt (Z i) x) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ I, ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) :=
      Finset.sum_le_sum hlength
    _ = ENNReal.ofReal (I.card : ℝ) *
        ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) := by
      simp [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 + 1) *
        ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) := by
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast hcard
    _ = ENNReal.ofReal (filterBadDirectionLength N E) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ) ^ 2 + 1)]
      congr 1
      dsimp [filterBadDirectionLength]
      ring

/-- The literal product of all test masks at a pin and direction. -/
def finiteDirectionalSymbol {ι : Type*} (I : Finset ι)
    (b : ι → Plane → UnitCircle → ℝ) (x : Plane) (w : UnitCircle) : ℝ :=
  ∏ i ∈ I, b i x w

theorem measurable_finiteDirectionalSymbol {ι : Type*} {I : Finset ι}
    {b : ι → Plane → UnitCircle → ℝ}
    (hb : ∀ i ∈ I, Measurable (Function.uncurry (b i))) :
    Measurable (Function.uncurry (finiteDirectionalSymbol I b)) := by
  exact I.measurable_prod hb

theorem finiteDirectionalSymbol_mem_Icc {ι : Type*} (I : Finset ι)
    {b : ι → Plane → UnitCircle → ℝ}
    (hb : ∀ i ∈ I, ∀ x w, b i x w ∈ Icc 0 1) (x : Plane) (w : UnitCircle) :
    finiteDirectionalSymbol I b x w ∈ Icc 0 1 := by
  classical
  unfold finiteDirectionalSymbol
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi]
    have hnew := hb i (Finset.mem_insert_self _ _) x w
    have hold := ih (fun j hj ↦ hb j (Finset.mem_insert_of_mem hj))
    exact ⟨mul_nonneg hnew.1 hold.1, by nlinarith [hnew.1, hnew.2, hold.1, hold.2]⟩

/-- A finite product is one whenever no test fails in the actual finite union. -/
theorem finiteDirectionalSymbol_eq_one_off_badDirections {ι : Type*} {I : Finset ι}
    {Z : ι → Set (Plane × UnitCircle)} {b : ι → Plane → UnitCircle → ℝ}
    {C : Set Plane}
    (hgood : ∀ i ∈ I, ∀ x ∈ C, ∀ w, (x, w) ∉ Z i → b i x w = 1)
    {x : Plane} (hx : x ∈ C) {w : UnitCircle}
    (hw : (x, w) ∉ finiteBadDirections I Z) : finiteDirectionalSymbol I b x w = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply hgood i hi x hx w
  intro hbad
  exact hw (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hi, hbad⟩⟩)

/-- The finite test product is set to zero outside its actual regular carrier. -/
def carrierDirectionalSymbol {ι : Type*} (C : Set Plane) (I : Finset ι)
    (b : ι → Plane → UnitCircle → ℝ) (x : Plane) (w : UnitCircle) : ℝ := by
  classical
  exact if x ∈ C then finiteDirectionalSymbol I b x w else 0

theorem measurable_carrierDirectionalSymbol {ι : Type*} {C : Set Plane}
    (hC : MeasurableSet C) {I : Finset ι} {b : ι → Plane → UnitCircle → ℝ}
    (hb : ∀ i ∈ I, Measurable (Function.uncurry (b i))) :
    Measurable (Function.uncurry (carrierDirectionalSymbol C I b)) := by
  unfold Function.uncurry carrierDirectionalSymbol
  apply Measurable.ite (hC.preimage measurable_fst)
    (measurable_finiteDirectionalSymbol hb) measurable_const

theorem carrierDirectionalSymbol_mem_Icc {ι : Type*} (C : Set Plane) (I : Finset ι)
    {b : ι → Plane → UnitCircle → ℝ}
    (hb : ∀ i ∈ I, ∀ x w, b i x w ∈ Icc 0 1) (x : Plane) (w : UnitCircle) :
    carrierDirectionalSymbol C I b x w ∈ Icc 0 1 := by
  unfold carrierDirectionalSymbol
  split_ifs
  · exact finiteDirectionalSymbol_mem_Icc I hb x w
  · simp

theorem carrierDirectionalSymbol_eq_one_off_badDirections {ι : Type*} {I : Finset ι}
    {Z : ι → Set (Plane × UnitCircle)} {b : ι → Plane → UnitCircle → ℝ} {C : Set Plane}
    (hgood : ∀ i ∈ I, ∀ x ∈ C, ∀ w, (x, w) ∉ Z i → b i x w = 1)
    {x : Plane} (hx : x ∈ C) {w : UnitCircle}
    (hw : (x, w) ∉ finiteBadDirections I Z) : carrierDirectionalSymbol C I b x w = 1 := by
  rw [carrierDirectionalSymbol, ite_eq_left hx]
  exact finiteDirectionalSymbol_eq_one_off_badDirections hgood hx hw

end FalconerThetaGauge
