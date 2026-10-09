module

public import FalconerThetaGauge.DirectionalTestsRecords
public import FalconerThetaGauge.FilteredDistanceMeasureFiniteTests

/-! # The actual finite directional filter made from scheduled tests and occupied cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

open GaugeFrostman

/-- The actual Borel failure set, with a separate literal test on every occupied anchor cell. -/
def scheduledTestFailureSet (ρ : Measure Plane) (E : ℝ) (test : ProfileScheduleTest) :
    Set (Plane × UnitCircle) :=
  ⋃ P ∈ occupiedUnitCells ρ test.anchor,
    dyadicCube test.anchor P ×ˢ (scheduledPassingDirections ρ E 2 test P)ᶜ

theorem measurableSet_scheduledTestFailureSet (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) (test : ProfileScheduleTest) : MeasurableSet (scheduledTestFailureSet ρ E test) :=
  MeasurableSet.biUnion (occupiedUnitCells ρ test.anchor).countable_toSet
    (fun P _ ↦ (measurableSet_dyadicCube test.anchor P).prod
      (measurableSet_scheduledPassingDirections ρ E 2 test P).compl)

theorem mem_scheduledTestFailureSet_iff (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) (x : Plane) (w : UnitCircle) :
    (x, w) ∈ scheduledTestFailureSet ρ E test ↔
      ∃ P ∈ occupiedUnitCells ρ test.anchor,
        x ∈ dyadicCube test.anchor P ∧ w ∉ scheduledPassingDirections ρ E 2 test P := by
  simp only [scheduledTestFailureSet, mem_iUnion, exists_prop, mem_prod, mem_compl_iff]

theorem scheduledTestFailureSet_symmetric (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) : IsSymmetricBadDirections (scheduledTestFailureSet ρ E test) := by
  intro x w
  simp only [mem_scheduledTestFailureSet_iff,
    scheduledPassingDirections_antipodal]

theorem scheduledTestFailureSet_section_on_cell (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) {P : Fin 2 → ℤ} (hP : P ∈ occupiedUnitCells ρ test.anchor)
    {x : Plane} (hx : x ∈ dyadicCube test.anchor P) :
    badDirectionsAt (scheduledTestFailureSet ρ E test) x =
      (scheduledPassingDirections ρ E 2 test P)ᶜ := by
  ext w
  change (x, w) ∈ scheduledTestFailureSet ρ E test ↔
    w ∈ (scheduledPassingDirections ρ E 2 test P)ᶜ
  rw [mem_scheduledTestFailureSet_iff]
  constructor
  · rintro ⟨Q, _, hxQ, hw⟩
    have hQP : Q = P := (mem_dyadicCube_iff.mp hxQ).symm.trans (mem_dyadicCube_iff.mp hx)
    simpa only [hQP, mem_compl_iff] using hw
  · intro hw
    exact ⟨P, hP, hx, hw⟩

theorem scheduledTestFailureSet_section_off_cells (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) {x : Plane}
    (hx : ∀ P ∈ occupiedUnitCells ρ test.anchor, x ∉ dyadicCube test.anchor P) :
    badDirectionsAt (scheduledTestFailureSet ρ E test) x = ∅ := by
  ext w
  change (x, w) ∈ scheduledTestFailureSet ρ E test ↔ w ∈ (∅ : Set UnitCircle)
  simp only [mem_scheduledTestFailureSet_iff, mem_empty_iff_false, iff_false]
  rintro ⟨P, hP, hxP, _⟩
  exact hx P hP hxP

/-- Every pin's literal test-failure section has the source's exact Markov length. -/
theorem scheduledTestFailureSet_short (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) (test : ProfileScheduleTest) (x : Plane) :
    circleArcLength (badDirectionsAt (scheduledTestFailureSet ρ E test) x) ≤
      ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) := by
  by_cases hx : ∃ P ∈ occupiedUnitCells ρ test.anchor, x ∈ dyadicCube test.anchor P
  · obtain ⟨P, hP, hxP⟩ := hx
    rw [scheduledTestFailureSet_section_on_cell ρ E test hP hxP]
    exact circleArcLength_scheduled_failure_le ρ E test P (Finset.mem_filter.mp hP).2
  · rw [scheduledTestFailureSet_section_off_cells ρ E test
      (by simpa only [not_exists, not_and] using hx), measure_empty]
    exact bot_le

theorem occupiedUnitCells_pairwiseDisjoint (ρ : Measure Plane) (p : ℕ) :
    (occupiedUnitCells ρ p : Set (Fin 2 → ℤ)).PairwiseDisjoint (dyadicCube p) := by
  intro P _ Q _ hPQ
  exact dyadicCube_disjoint hPQ

/-- The literal finite anchor-cell mask at width two, jointly in pin and direction. -/
def scheduledTestSymbol (ρ : Measure Plane) (E : ℝ) (test : ProfileScheduleTest)
    (K : ℕ) : Plane → UnitCircle → ℝ :=
  partitionCirclePassingSymbol K (scheduledMaskScale E test) (occupiedUnitCells ρ test.anchor)
    (dyadicCube test.anchor) (fun P ↦ scheduledPassingDirections ρ E 2 test P)

theorem measurable_scheduledTestSymbol (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) :
    Measurable (Function.uncurry (scheduledTestSymbol ρ E test K)) :=
  measurable_partitionCirclePassingSymbol K (scheduledMaskScale_pos E test)
    (fun P _ ↦ measurableSet_dyadicCube test.anchor P) _

theorem scheduledTestSymbol_mem_Icc (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (x : Plane) (w : UnitCircle) :
    scheduledTestSymbol ρ E test K x w ∈ Icc 0 1 :=
  partitionCirclePassingSymbol_mem_Icc K (scheduledMaskScale_pos E test)
    (occupiedUnitCells_pairwiseDisjoint ρ test.anchor) _ x w

theorem scheduledTestSymbol_eq_on_cell (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) {P : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ test.anchor) {x : Plane}
    (hx : x ∈ dyadicCube test.anchor P) (w : UnitCircle) :
    scheduledTestSymbol ρ E test K x w =
      circlePassingMask K (scheduledMaskScale E test) (scheduledPassingDirections ρ E 2 test P) w :=
  partitionDirectionalSymbol_eq_on_cell (occupiedUnitCells_pairwiseDisjoint ρ test.anchor)
    _ hP hx w

theorem contDiff_scheduledTestSymbol_comp_angle (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (x : Plane) :
    ContDiff ℝ ∞ (fun θ ↦ scheduledTestSymbol ρ E test K x (unitCircleOfAngle θ)) := by
  by_cases hx : ∃ P ∈ occupiedUnitCells ρ test.anchor, x ∈ dyadicCube test.anchor P
  · obtain ⟨P, hP, hxP⟩ := hx
    have heq : (fun θ ↦ scheduledTestSymbol ρ E test K x (unitCircleOfAngle θ)) =
        fun θ ↦ circlePassingMask K (scheduledMaskScale E test)
          (scheduledPassingDirections ρ E 2 test P) (unitCircleOfAngle θ) :=
      funext (fun θ ↦ scheduledTestSymbol_eq_on_cell ρ E test K hP hxP _)
    rw [heq]
    exact contDiff_circlePassingMask_comp_angle K (scheduledMaskScale_pos E test) _
  · have hnone : ∀ P ∈ occupiedUnitCells ρ test.anchor, x ∉ dyadicCube test.anchor P :=
      by simpa only [not_exists, not_and] using hx
    have heq : (fun θ ↦ scheduledTestSymbol ρ E test K x (unitCircleOfAngle θ)) =
        fun _ : ℝ ↦ 0 := by
      ext θ
      exact partitionDirectionalSymbol_eq_zero_off_cells _ _ _ hnone _
    rw [heq]
    exact contDiff_const

theorem norm_iteratedDeriv_scheduledTestSymbol_comp_angle_le (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) {T : ℕ} (hT : 2 ≤ T) {k : ℕ} (hk : k ≤ 6 * T)
    (x : Plane) (θ : ℝ) :
    ‖iteratedDeriv k (fun θ ↦ scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle θ)) θ‖ ≤
      ((4 * (T : ℝ)) ^ 3 / scheduledMaskScale E test) ^ k := by
  by_cases hx : ∃ P ∈ occupiedUnitCells ρ test.anchor, x ∈ dyadicCube test.anchor P
  · obtain ⟨P, hP, hxP⟩ := hx
    have heq : (fun θ ↦ scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle θ)) =
        fun θ ↦ circlePassingMask (6 * T) (scheduledMaskScale E test)
          (scheduledPassingDirections ρ E 2 test P) (unitCircleOfAngle θ) :=
      funext (fun θ ↦ scheduledTestSymbol_eq_on_cell ρ E test (6 * T) hP hxP _)
    rw [heq]
    exact norm_iteratedDeriv_circlePassingMask_comp_angle_le hT hk
      (scheduledMaskScale_pos E test) _ θ
  · have hnone : ∀ P ∈ occupiedUnitCells ρ test.anchor, x ∉ dyadicCube test.anchor P :=
      by simpa only [not_exists, not_and] using hx
    have heq : (fun θ ↦ scheduledTestSymbol ρ E test (6 * T) x (unitCircleOfAngle θ)) =
        fun _ : ℝ ↦ 0 := by
      ext θ
      exact partitionDirectionalSymbol_eq_zero_off_cells _ _ _ hnone _
    rw [heq]
    simp only [iteratedDeriv_const, ite_self, norm_zero]
    have hδ := scheduledMaskScale_pos E test
    positivity

theorem scheduledTestSymbol_passing (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) {x : Plane}
    (hx : x ∈ cellUnion test.anchor (occupiedUnitCells ρ test.anchor)) {w : UnitCircle}
    (hw : (x, w) ∉ scheduledTestFailureSet ρ E test) : scheduledTestSymbol ρ E test K x w = 1 := by
  obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hx
  apply partitionCirclePassingSymbol_eq_one_on_cell K (scheduledMaskScale_pos E test)
    (occupiedUnitCells_pairwiseDisjoint ρ test.anchor) _ hP hxP
  by_contra hnot
  exact hw ((mem_scheduledTestFailureSet_iff ρ E test x w).mpr ⟨P, hP, hxP, hnot⟩)

/-- An actual finite filter of scheduled tests, with every obligation proved from
the literal counts and quantitative convolution masks. Carrier coverage is the
geometric condition that its points lie in occupied anchors at every listed depth. -/
def scheduledDirectionalFilter (ρ : Measure Plane) [IsFiniteMeasure ρ] (N : ℕ) (E : ℝ)
    (K : ℕ) (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (C : Set Plane) (hC : MeasurableSet C)
    (hcoverage : ∀ test ∈ I, C ⊆ cellUnion test.anchor (occupiedUnitCells ρ test.anchor)) :
    FiniteDirectionalFilter N E where
  carrier := C
  carrier_measurable := hC
  testCount := I.card
  testCount_le := hcard
  badTest i := scheduledTestFailureSet ρ E ((I.equivFin.symm i).val)
  badTest_measurable i := measurableSet_scheduledTestFailureSet ρ E (I.equivFin.symm i).val
  badTest_symmetric i := scheduledTestFailureSet_symmetric ρ E (I.equivFin.symm i).val
  badTest_short i := scheduledTestFailureSet_short ρ E (I.equivFin.symm i).val
  maskTest i := scheduledTestSymbol ρ E ((I.equivFin.symm i).val) K
  maskTest_measurable i := measurable_scheduledTestSymbol ρ E (I.equivFin.symm i).val K
  maskTest_range i := scheduledTestSymbol_mem_Icc ρ E (I.equivFin.symm i).val K
  maskTest_passing i _x hx _w hw := scheduledTestSymbol_passing ρ E (I.equivFin.symm i).val K
    (hcoverage _ (I.equivFin.symm i).property hx) hw

end FalconerThetaGauge
