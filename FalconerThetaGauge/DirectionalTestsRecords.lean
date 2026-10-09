module

public import FalconerThetaGauge.DirectionalTestsProjection
public import FalconerThetaGauge.RegularMeasureEntryTests
public import FalconerThetaGauge.ExplicitBumpPartition

/-! # Literal directional counts and masks attached to actual scheduled test records -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem tubeCount_eq_card (ρ : Measure Plane) (g p : ℕ) (E width : ℝ)
    (P : Fin 2 → ℤ) (w : UnitCircle) : tubeCount ρ g p E width P w =
      (((occupiedUnitCells ρ p).filter (fun Q ↦ dyadicCellCenter p Q ∈
        directionalTube g p E width (dyadicCellCenter p P) w)).card : ℝ) := by
  simp only [tubeCount, indicator, mem_ofPred_eq]
  exact Finset.sum_boole _ _

/-- The actual tube/projection count selected by the finite-depth test record. -/
def scheduledDirectionalCount (ρ : Measure Plane) (E width : ℝ) (test : ProfileScheduleTest)
    (P : Fin 2 → ℤ) : UnitCircle → ℝ :=
  match test.kind with
  | .tube => tubeCount ρ test.endpoint test.anchor E width P
  | .projection => projectionCount ρ test.anchor test.endpoint E width P

theorem measurable_scheduledDirectionalCount (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E width : ℝ) (test : ProfileScheduleTest) (P : Fin 2 → ℤ) :
    Measurable (scheduledDirectionalCount ρ E width test P) := by
  cases h : test.kind
  · simpa only [scheduledDirectionalCount, h] using
      measurable_tubeCount ρ test.endpoint test.anchor E width P
  · simpa only [scheduledDirectionalCount, h, projectionCount] using
      measurable_projectionCountOfMeasure (projectionAnchorMeasure ρ test.anchor P)
        test.endpoint E width

theorem scheduledDirectionalCount_nonneg (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (P : Fin 2 → ℤ) (w : UnitCircle) :
    0 ≤ scheduledDirectionalCount ρ E width test P w := by
  cases h : test.kind <;> simp only [scheduledDirectionalCount, h, projectionCount]
  · exact tubeCount_nonneg ρ test.endpoint test.anchor E width P w
  · exact projectionCountOfMeasure_nonneg _ test.endpoint E width w

theorem integrable_scheduledDirectionalCount (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E width : ℝ) (test : ProfileScheduleTest) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ test.anchor P) :
    Integrable (scheduledDirectionalCount ρ E width test P) circleArcLength := by
  cases h : test.kind <;> simp only [scheduledDirectionalCount, h, projectionCount]
  · exact integrable_tubeCount ρ test.endpoint test.anchor E width P
  · have := isProbabilityMeasure_projectionAnchorMeasure ρ test.anchor P hP
    exact integrable_projectionCountOfMeasure _ test.endpoint E width

theorem scheduledDirectionalCount_antipodal (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (P : Fin 2 → ℤ) (w : UnitCircle) :
    scheduledDirectionalCount ρ E width test P (circleAntipode w) =
      scheduledDirectionalCount ρ E width test P w := by
  cases h : test.kind <;> simp only [scheduledDirectionalCount, h, projectionCount]
  · exact tubeCount_antipodal ρ test.endpoint test.anchor E width P w
  · exact projectionCountOfMeasure_antipodal _ test.endpoint E width w

theorem scheduledDirectionalCount_mono_width (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) {width width' : ℝ} (hwidth : width ≤ width') (test : ProfileScheduleTest)
    (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P) (w : UnitCircle) :
    scheduledDirectionalCount ρ E width test P w ≤
      scheduledDirectionalCount ρ E width' test P w := by
  cases h : test.kind <;> simp only [scheduledDirectionalCount, h, projectionCount]
  · exact tubeCount_mono_width ρ test.endpoint test.anchor E hwidth P w
  · have := isProbabilityMeasure_projectionAnchorMeasure ρ test.anchor P hP
    exact projectionCountOfMeasure_mono_width _ test.endpoint E hwidth w

/-- The width-two average of the actual scheduled directional count. -/
def scheduledDirectionalAverage (ρ : Measure Plane) (E : ℝ) (test : ProfileScheduleTest)
    (P : Fin 2 → ℤ) : ℝ := directionalAverage (scheduledDirectionalCount ρ E 2 test P)

/-- The exact passing test at an arbitrary width, always against the width-two average. -/
def scheduledPassingDirections (ρ : Measure Plane) (E width : ℝ) (test : ProfileScheduleTest)
    (P : Fin 2 → ℤ) : Set UnitCircle :=
  {w | scheduledDirectionalCount ρ E width test P w ≤
    (2 : ℝ) ^ (2 * E) * scheduledDirectionalAverage ρ E test P}

theorem measurableSet_scheduledPassingDirections (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E width : ℝ) (test : ProfileScheduleTest) (P : Fin 2 → ℤ) :
    MeasurableSet (scheduledPassingDirections ρ E width test P) :=
  measurableSet_le (measurable_scheduledDirectionalCount ρ E width test P) measurable_const

theorem scheduledPassingDirections_antipodal (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (P : Fin 2 → ℤ) (w : UnitCircle) :
    circleAntipode w ∈ scheduledPassingDirections ρ E width test P ↔
      w ∈ scheduledPassingDirections ρ E width test P := by
  simp only [scheduledPassingDirections, mem_ofPred_eq, scheduledDirectionalCount_antipodal]

theorem scheduledPassingDirections_mono_width (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) {width width' : ℝ} (hwidth : width ≤ width') (test : ProfileScheduleTest)
    (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P) :
    scheduledPassingDirections ρ E width' test P ⊆ scheduledPassingDirections ρ E width test P := by
  intro w hw
  exact (scheduledDirectionalCount_mono_width ρ E hwidth test P hP w).trans hw

theorem circleArcLength_scheduled_failure_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) (test : ProfileScheduleTest) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ test.anchor P) :
    circleArcLength (scheduledPassingDirections ρ E 2 test P)ᶜ ≤
      ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) := by
  have h := circleArcLength_directionalTestFailure_le (q := (2 : ℝ) ^ (2 * E))
    (Real.rpow_pos_of_pos (by norm_num) _)
    (integrable_scheduledDirectionalCount ρ E 2 test P hP)
    (scheduledDirectionalCount_nonneg ρ E 2 test P)
  have heq : (scheduledPassingDirections ρ E 2 test P)ᶜ =
      directionalTestFailure ((2 : ℝ) ^ (2 * E)) (scheduledDirectionalCount ρ E 2 test P) := by
    ext w
    simp only [scheduledPassingDirections, directionalTestFailure, mem_compl_iff,
      mem_ofPred_eq, not_le, scheduledDirectionalAverage]
  rw [heq]
  convert h using 1
  rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [neg_mul]

/-- The exact angular radius `min(1,2^(-ℓ)R^ε)` of the scheduled test mask. -/
def scheduledMaskScale (E : ℝ) (test : ProfileScheduleTest) : ℝ :=
  min 1 ((2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ E)

theorem scheduledMaskScale_pos (E : ℝ) (test : ProfileScheduleTest) :
    0 < scheduledMaskScale E test := by
  unfold scheduledMaskScale
  positivity

/-- The actual source mask of one recorded test at one occupied anchor. -/
def scheduledCircleMask (ρ : Measure Plane) (E width : ℝ) (test : ProfileScheduleTest)
    (K : ℕ) (P : Fin 2 → ℤ) : UnitCircle → ℝ :=
  circlePassingMask K (scheduledMaskScale E test) (scheduledPassingDirections ρ E width test P)

theorem measurable_scheduledCircleMask (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (P : Fin 2 → ℤ) :
    Measurable (scheduledCircleMask ρ E width test K P) :=
  measurable_circlePassingMask K (scheduledMaskScale_pos E test) _

theorem scheduledCircleMask_mem_Icc (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (P : Fin 2 → ℤ) (w : UnitCircle) :
    scheduledCircleMask ρ E width test K P w ∈ Icc 0 1 :=
  circlePassingMask_mem_Icc K (scheduledMaskScale_pos E test) _ _

theorem scheduledCircleMask_eq_one_on_passing (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (P : Fin 2 → ℤ) {w : UnitCircle}
    (hw : w ∈ scheduledPassingDirections ρ E width test P) :
    scheduledCircleMask ρ E width test K P w = 1 :=
  circlePassingMask_eq_one K (scheduledMaskScale_pos E test) hw

theorem scheduledCircleMask_antipodal (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (P : Fin 2 → ℤ) (w : UnitCircle) :
    scheduledCircleMask ρ E width test K P (circleAntipode w) =
      scheduledCircleMask ρ E width test K P w :=
  circlePassingMask_antipodal K _ _ (scheduledPassingDirections_antipodal ρ E width test P) w

end FalconerThetaGauge
