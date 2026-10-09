module

public import FalconerThetaGauge.MaskedDistanceEnergyDyadic
public import FalconerThetaGauge.MaskedFourierEnergyReached

/-! # Actual level masks and their genuine passing-set relations -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The literal scheduled anchor-cell convolution mask at an arbitrary source width. -/
def scheduledWidthTestSymbol (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) : Plane → UnitCircle → ℝ :=
  partitionCirclePassingSymbol K (scheduledMaskScale E test) (occupiedUnitCells ρ test.anchor)
    (dyadicCube test.anchor) (fun P ↦ scheduledPassingDirections ρ E width test P)

theorem measurable_scheduledWidthTestSymbol (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) :
    Measurable (uncurry (scheduledWidthTestSymbol ρ E width test K)) :=
  measurable_partitionCirclePassingSymbol K (scheduledMaskScale_pos E test)
    (fun P _ ↦ measurableSet_dyadicCube test.anchor P) _

theorem scheduledWidthTestSymbol_mem_Icc (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (x : Plane) (w : UnitCircle) :
    scheduledWidthTestSymbol ρ E width test K x w ∈ Icc 0 1 :=
  partitionCirclePassingSymbol_mem_Icc K (scheduledMaskScale_pos E test)
    (occupiedUnitCells_pairwiseDisjoint ρ test.anchor) _ x w

theorem scheduledWidthTestSymbol_eq_on_cell (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) {P : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ test.anchor) {x : Plane}
    (hx : x ∈ dyadicCube test.anchor P) (w : UnitCircle) :
    scheduledWidthTestSymbol ρ E width test K x w = scheduledCircleMask ρ E width test K P w :=
  partitionDirectionalSymbol_eq_on_cell (occupiedUnitCells_pairwiseDisjoint ρ test.anchor)
    _ hP hx w

/-- The genuine finite product at a fixed source level width. -/
def scheduledWidthMaskProduct (ρ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) : Plane → UnitCircle → ℝ :=
  fun x w ↦ ∏ test ∈ I, scheduledWidthTestSymbol ρ E width test K x w

theorem measurable_scheduledWidthMaskProduct (ρ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) :
    Measurable (uncurry (scheduledWidthMaskProduct ρ E width K I)) :=
  Finset.measurable_prod I fun test _ ↦ measurable_scheduledWidthTestSymbol ρ E width test K

theorem scheduledWidthMaskProduct_mem_Icc (ρ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (x : Plane) (w : UnitCircle) :
    scheduledWidthMaskProduct ρ E width K I x w ∈ Icc 0 1 := by
  constructor
  · exact Finset.prod_nonneg fun test _ ↦ (scheduledWidthTestSymbol_mem_Icc ρ E width test K x w).1
  · exact Finset.prod_le_one₀
      (fun test _ ↦ (scheduledWidthTestSymbol_mem_Icc ρ E width test K x w).1)
      (fun test _ ↦ (scheduledWidthTestSymbol_mem_Icc ρ E width test K x w).2)

/-- The actual finite family of occupied anchor carriers for this list. -/
def scheduledAnchorCarrier (ρ : Measure Plane) (I : Finset ProfileScheduleTest) : Set Plane :=
  ⋂ test ∈ I, cellUnion test.anchor (occupiedUnitCells ρ test.anchor)

theorem measurableSet_scheduledAnchorCarrier (ρ : Measure Plane) (I : Finset ProfileScheduleTest) :
    MeasurableSet (scheduledAnchorCarrier ρ I) :=
  MeasurableSet.biInter I.countable_toSet fun _test _ ↦ measurableSet_cellUnion _ _

/-- The actual occupied cells have full probability; omitted cells have genuinely zero mass. -/
theorem measure_cellUnion_occupiedUnitCells (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) (n : ℕ) : ρ (cellUnion n (occupiedUnitCells ρ n)) = 1 := by
  have hsum : (∑ P ∈ occupiedUnitCells ρ n, unitCellWeight ρ n P) =
      ∑ P ∈ unitCellIndices n, unitCellWeight ρ n P := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro P hP hnot
    have hn : ¬0 < unitCellWeight ρ n P := by
      intro hpos
      exact hnot (Finset.mem_filter.2 ⟨hP, hpos⟩)
    exact le_antisymm (le_of_not_gt hn) (unitCellWeight_nonneg ρ n P)
  have hreal : ρ.real (cellUnion n (occupiedUnitCells ρ n)) = 1 := by
    rw [real_cellUnion, hsum, sum_unitCellWeight_eq_one ρ n hρ]
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _), ← Measure.real, hreal]
  simp

theorem measure_scheduledAnchorCarrier (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) (I : Finset ProfileScheduleTest) :
    ρ (scheduledAnchorCarrier ρ I) = 1 := by
  have hae : ∀ᵐ x ∂ρ, ∀ test ∈ I, x ∈ cellUnion test.anchor (occupiedUnitCells ρ test.anchor) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert test I hnot ih =>
      have ht : ∀ᵐ x ∂ρ, x ∈ cellUnion test.anchor (occupiedUnitCells ρ test.anchor) :=
        (ae_mem_iff_measure_eq (measurableSet_cellUnion _ _).nullMeasurableSet).2
          (by simp [measure_cellUnion_occupiedUnitCells ρ hρ])
      filter_upwards [ht, ih] with x hx hI
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hx
      · exact hI u hu
  have hmem : ∀ᵐ x ∂ρ, x ∈ scheduledAnchorCarrier ρ I := by
    simpa only [scheduledAnchorCarrier, mem_iInter] using hae
  simpa only [measure_univ] using
    (ae_mem_iff_measure_eq (measurableSet_scheduledAnchorCarrier ρ I).nullMeasurableSet).1 hmem

/-- The true symbol equals one wherever all the listed literal tests pass at this width. -/
theorem scheduledWidthMaskProduct_eq_one_of_passing (ρ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) {x : Plane} (hx : x ∈ scheduledAnchorCarrier ρ I)
    (w : UnitCircle) (hw : ∀ test ∈ I, (x, w) ∈ scheduledPassingPinSet ρ E width test) :
    scheduledWidthMaskProduct ρ E width K I x w = 1 := by
  apply Finset.prod_eq_one
  intro test ht
  obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.1 (mem_iInter₂.1 hx test ht)
  rw [scheduledWidthTestSymbol_eq_on_cell ρ E width test K hP hxP]
  exact circlePassingMask_eq_one K (scheduledMaskScale_pos E test)
    ((mem_scheduledPassingPinSet_on_cell ρ E width test hP hxP w).1 (hw test ht))

/-- Every nonzero literal level product certifies passing every next-level test (L2). -/
theorem scheduledWidthMaskProduct_ne_zero_implies_next_passing
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {L : ℕ} (hL : 0 < L)
    (hsize : (L : ℝ) ≤ (2 : ℝ) ^ E / 8) (i K : ℕ) (I : Finset ProfileScheduleTest)
    (htube : ∀ test ∈ I, test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : ∀ test ∈ I, test.kind = .projection → test.anchor ≤ test.endpoint)
    {x : Plane} (hx : x ∈ scheduledAnchorCarrier ρ I) (w : UnitCircle)
    (hprod : scheduledWidthMaskProduct ρ E (directionalLevelWidth L i) K I x w ≠ 0) :
    ∀ test ∈ I, (x, w) ∈ scheduledPassingPinSet ρ E (directionalLevelWidth L (i + 1)) test := by
  intro test ht
  obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.1 (mem_iInter₂.1 hx test ht)
  have hf := (Finset.prod_ne_zero_iff.1 hprod) test ht
  rw [scheduledWidthTestSymbol_eq_on_cell ρ E _ test K hP hxP] at hf
  apply (mem_scheduledPassingPinSet_on_cell ρ E _ test hP hxP w).2
  have hθ : iteratedDeriv 0 (fun θ ↦ scheduledCircleMask ρ E (directionalLevelWidth L i)
      test K P (unitCircleOfAngle θ)) (circleAngle w) ≠ 0 := by
    simpa only [iteratedDeriv_zero, unitCircleOfAngle_circleAngle] using hf
  simpa only [unitCircleOfAngle_circleAngle] using
    scheduled_level_derivative_ne_zero_implies_passing ρ E hL hsize i test
      (htube test ht) (hprojection test ht) K 0 P (Finset.mem_filter.1 hP).2 hθ

end FalconerThetaGauge
