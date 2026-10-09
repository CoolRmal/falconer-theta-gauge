module

public import FalconerThetaGauge.ExplicitBumpCircle

/-!
# Jointly Borel masks from the actual finite partition into occupied anchor cells

At a fixed scale the angular test data are constant on each occupied anchor cell.
Constructing each circle mask first and then taking this finite Borel partition
avoids any unjustified measurability claim for arbitrary varying set fibers.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- A literal finite symbol with one fixed angular mask on each Borel planar cell. -/
def partitionDirectionalSymbol {ι : Type*} (I : Finset ι) (C : ι → Set Plane)
    (b : ι → UnitCircle → ℝ) (x : Plane) (w : UnitCircle) : ℝ :=
  ∑ i ∈ I, (C i).indicator (fun _ ↦ b i w) x

theorem measurable_partitionDirectionalSymbol {ι : Type*} {I : Finset ι}
    {C : ι → Set Plane} {b : ι → UnitCircle → ℝ}
    (hC : ∀ i ∈ I, MeasurableSet (C i)) (hb : ∀ i ∈ I, Measurable (b i)) :
    Measurable (Function.uncurry (partitionDirectionalSymbol I C b)) := by
  change Measurable (fun p : Plane × UnitCircle ↦
    ∑ i ∈ I, (C i).indicator (fun _ ↦ b i p.2) p.1)
  apply I.measurable_sum
  intro i hi
  have heq : (fun p : Plane × UnitCircle ↦ (C i).indicator (fun _ ↦ b i p.2) p.1) =
      (Prod.fst ⁻¹' C i).indicator (fun p : Plane × UnitCircle ↦ b i p.2) := by
    ext p
    by_cases hp : p.1 ∈ C i <;> simp [hp]
  rw [heq]
  exact ((hb i hi).comp measurable_snd).indicator ((hC i hi).preimage measurable_fst)

theorem partitionDirectionalSymbol_eq_on_cell {ι : Type*} {I : Finset ι}
    {C : ι → Set Plane} (hdisjoint : (I : Set ι).PairwiseDisjoint C)
    (b : ι → UnitCircle → ℝ) {i : ι} (hi : i ∈ I) {x : Plane} (hx : x ∈ C i)
    (w : UnitCircle) : partitionDirectionalSymbol I C b x w = b i w := by
  rw [partitionDirectionalSymbol, Finset.sum_eq_single i, indicator_of_mem hx]
  · intro j hj hji
    apply indicator_of_notMem
    intro hxj
    exact hji ((Set.pairwiseDisjoint_iff.mp hdisjoint) hj hi ⟨x, hxj, hx⟩)
  · intro h
    exact False.elim (h hi)

theorem partitionDirectionalSymbol_eq_zero_off_cells {ι : Type*} (I : Finset ι)
    (C : ι → Set Plane) (b : ι → UnitCircle → ℝ) {x : Plane}
    (hx : ∀ i ∈ I, x ∉ C i) (w : UnitCircle) : partitionDirectionalSymbol I C b x w = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact indicator_of_notMem (hx i hi) _

theorem partitionDirectionalSymbol_mem_Icc {ι : Type*} {I : Finset ι}
    {C : ι → Set Plane} (hdisjoint : (I : Set ι).PairwiseDisjoint C)
    {b : ι → UnitCircle → ℝ} (hb : ∀ i ∈ I, ∀ w, b i w ∈ Icc 0 1)
    (x : Plane) (w : UnitCircle) : partitionDirectionalSymbol I C b x w ∈ Icc 0 1 := by
  classical
  by_cases hx : ∃ i ∈ I, x ∈ C i
  · obtain ⟨i, hi, hxi⟩ := hx
    rw [partitionDirectionalSymbol_eq_on_cell hdisjoint b hi hxi]
    exact hb i hi w
  · rw [partitionDirectionalSymbol_eq_zero_off_cells I C b
      (by simpa only [not_exists, not_and] using hx)]
    simp

theorem partitionDirectionalSymbol_antipodal {ι : Type*} (I : Finset ι)
    (C : ι → Set Plane) {b : ι → UnitCircle → ℝ}
    (hb : ∀ i ∈ I, ∀ w, b i (circleAntipode w) = b i w) (x : Plane) (w : UnitCircle) :
    partitionDirectionalSymbol I C b x (circleAntipode w) =
      partitionDirectionalSymbol I C b x w := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hb i hi]

/-- The actual finite Borel anchor-cell symbol made of the quantitative circle masks. -/
def partitionCirclePassingSymbol {ι : Type*} (K : ℕ) (δ : ℝ) (I : Finset ι)
    (C : ι → Set Plane) (Z : ι → Set UnitCircle) : Plane → UnitCircle → ℝ :=
  partitionDirectionalSymbol I C (fun i ↦ circlePassingMask K δ (Z i))

theorem measurable_partitionCirclePassingSymbol {ι : Type*} (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {I : Finset ι} {C : ι → Set Plane} (hC : ∀ i ∈ I, MeasurableSet (C i))
    (Z : ι → Set UnitCircle) :
    Measurable (Function.uncurry (partitionCirclePassingSymbol K δ I C Z)) :=
  measurable_partitionDirectionalSymbol hC (fun i _ ↦ measurable_circlePassingMask K hδ (Z i))

theorem partitionCirclePassingSymbol_mem_Icc {ι : Type*} (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {I : Finset ι} {C : ι → Set Plane} (hdisjoint : (I : Set ι).PairwiseDisjoint C)
    (Z : ι → Set UnitCircle) (x : Plane) (w : UnitCircle) :
    partitionCirclePassingSymbol K δ I C Z x w ∈ Icc 0 1 :=
  partitionDirectionalSymbol_mem_Icc hdisjoint (fun i _ ↦ circlePassingMask_mem_Icc K hδ (Z i)) x w

theorem partitionCirclePassingSymbol_eq_one_on_cell {ι : Type*} (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {I : Finset ι} {C : ι → Set Plane} (hdisjoint : (I : Set ι).PairwiseDisjoint C)
    (Z : ι → Set UnitCircle) {i : ι} (hi : i ∈ I) {x : Plane} (hx : x ∈ C i)
    {w : UnitCircle} (hw : w ∈ Z i) : partitionCirclePassingSymbol K δ I C Z x w = 1 := by
  rw [partitionCirclePassingSymbol, partitionDirectionalSymbol_eq_on_cell hdisjoint _ hi hx]
  exact circlePassingMask_eq_one K hδ hw

theorem partitionCirclePassingSymbol_antipodal {ι : Type*} (K : ℕ) (δ : ℝ)
    (I : Finset ι) (C : ι → Set Plane) (Z : ι → Set UnitCircle)
    (hZ : ∀ i ∈ I, ∀ w, circleAntipode w ∈ Z i ↔ w ∈ Z i) (x : Plane) (w : UnitCircle) :
    partitionCirclePassingSymbol K δ I C Z x (circleAntipode w) =
      partitionCirclePassingSymbol K δ I C Z x w :=
  partitionDirectionalSymbol_antipodal I C
    (fun i hi ↦ circlePassingMask_antipodal K δ (Z i) (hZ i hi)) x w

end FalconerThetaGauge
