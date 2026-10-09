module

public import FalconerThetaGauge.MaskedFourierEnergyFactors

/-! # Reached literal anchor tests can be removed from a dyadic-cell energy -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The true finite product of the scheduled convolution masks. -/
def scheduledMaskProduct (ρ : Measure Plane) (E : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) : Plane → UnitCircle → ℝ :=
  fun x w ↦ ∏ test ∈ I, scheduledTestSymbol ρ E test K x w

theorem measurable_scheduledMaskProduct (ρ : Measure Plane) (E : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) : Measurable (uncurry (scheduledMaskProduct ρ E K I)) :=
  Finset.measurable_prod I fun test _ ↦ measurable_scheduledTestSymbol ρ E test K

theorem scheduledMaskProduct_mem_Icc (ρ : Measure Plane) (E : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (x : Plane) (w : UnitCircle) :
    scheduledMaskProduct ρ E K I x w ∈ Icc 0 1 := by
  constructor
  · exact Finset.prod_nonneg fun test _ ↦ (scheduledTestSymbol_mem_Icc ρ E test K x w).1
  · exact Finset.prod_le_one₀ (fun test _ ↦ (scheduledTestSymbol_mem_Icc ρ E test K x w).1)
      (fun test _ ↦ (scheduledTestSymbol_mem_Icc ρ E test K x w).2)

theorem abs_scheduledMaskProduct_le_one (ρ : Measure Plane) (E : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (x : Plane) (w : UnitCircle) :
    |scheduledMaskProduct ρ E K I x w| ≤ 1 := by
  rw [abs_of_nonneg (scheduledMaskProduct_mem_Icc ρ E K I x w).1]
  exact (scheduledMaskProduct_mem_Icc ρ E K I x w).2

theorem occupiedUnitCells_ancestor_of_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {p a : ℕ} (hpa : p ≤ a) {P : Fin 2 → ℤ} (hP : P ∈ occupiedUnitCells ρ a) :
    ancestor (a - p) P ∈ occupiedUnitCells ρ p := by
  obtain ⟨hPU, hmass⟩ := Finset.mem_filter.1 hP
  have hne : ρ (dyadicCube a P) ≠ 0 := by
    intro hzero
    simp only [unitCellWeight, Measure.real, hzero, ENNReal.toReal_zero] at hmass
    linarith
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hne
  have hxa := mem_dyadicCube_ancestor_of_mem hpa hx
  have hparent : ancestor (a - p) P ∈ unitCellIndices p := by
    rw [← mem_dyadicCube_iff.1 hxa]
    exact cubeIndex_mem_unitCellIndices p (dyadicCube_subset_unitSquare a hPU hx)
  apply Finset.mem_filter.2 ⟨hparent, ?_⟩
  exact hmass.trans_le (measureReal_mono (fun y hy ↦ mem_dyadicCube_ancestor_of_mem hpa hy))

/-- The removed factors are actual functions of direction on the fixed fine cell. -/
def reachedScheduledMaskFactor (ρ : Measure Plane) (E : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (a : ℕ) (P : Fin 2 → ℤ) : UnitCircle → ℝ :=
  fun w ↦ ∏ test ∈ I.filter (fun test ↦ test.anchor ≤ a),
    circlePassingMask K (scheduledMaskScale E test)
      (scheduledPassingDirections ρ E 2 test (ancestor (a - test.anchor) P)) w

theorem reachedScheduledMaskFactor_mem_Icc (ρ : Measure Plane) (E : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (a : ℕ) (P : Fin 2 → ℤ) (w : UnitCircle) :
    reachedScheduledMaskFactor ρ E K I a P w ∈ Icc 0 1 := by
  constructor
  · exact Finset.prod_nonneg fun test _ ↦
      (circlePassingMask_mem_Icc K (scheduledMaskScale_pos E test) _ w).1
  · exact Finset.prod_le_one₀
      (fun test _ ↦ (circlePassingMask_mem_Icc K (scheduledMaskScale_pos E test) _ w).1)
      (fun test _ ↦ (circlePassingMask_mem_Icc K (scheduledMaskScale_pos E test) _ w).2)

/-- This exact factorization proves (S4) for every listed reached test on an actual cell. -/
theorem scheduledMaskProduct_eq_reached_mul (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (a : ℕ) {P : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ a) {x : Plane} (hx : x ∈ dyadicCube a P) (w : UnitCircle) :
    scheduledMaskProduct ρ E K I x w = reachedScheduledMaskFactor ρ E K I a P w *
      scheduledMaskProduct ρ E K (I.filter (fun test ↦ a < test.anchor)) x w := by
  rw [scheduledMaskProduct, ← Finset.prod_filter_mul_prod_filter_not I
    (fun test ↦ test.anchor ≤ a)]
  congr 1
  · apply Finset.prod_congr rfl
    intro test ht
    have hanchor := (Finset.mem_filter.1 ht).2
    exact scheduledTestSymbol_eq_on_cell ρ E test K
      (occupiedUnitCells_ancestor_of_le ρ hanchor hP)
      (mem_dyadicCube_ancestor_of_mem hanchor hx) w
  · simp only [scheduledMaskProduct, not_le]

/-- Reached literal tests may be dropped in the true Fourier energy on actual occupied cells. -/
theorem maskedFourierEnergy_scheduled_drop_reached (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (E : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (a : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ₁ a) (hQ : Q ∈ occupiedUnitCells ρ₂ a) (v : ℕ) :
    maskedFourierEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
        (scheduledMaskProduct ρ₁ E K I₁) (scheduledMaskProduct ρ₂ E K I₂) K v ≤
      maskedFourierEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
        (scheduledMaskProduct ρ₁ E K (I₁.filter (fun test ↦ a < test.anchor)))
        (scheduledMaskProduct ρ₂ E K (I₂.filter (fun test ↦ a < test.anchor))) K v := by
  apply maskedFourierEnergy_le_of_eqOn ρ₁ ρ₂
    (measurableSet_dyadicCube a P) (measurableSet_dyadicCube a Q)
    (measurable_scheduledMaskProduct ρ₁ E K _) (measurable_scheduledMaskProduct ρ₂ E K _)
    (measurable_scheduledMaskProduct ρ₁ E K _) (measurable_scheduledMaskProduct ρ₂ E K _)
    (abs_scheduledMaskProduct_le_one ρ₁ E K _) (abs_scheduledMaskProduct_le_one ρ₂ E K _)
    (abs_scheduledMaskProduct_le_one ρ₁ E K _) (abs_scheduledMaskProduct_le_one ρ₂ E K _)
    (reachedScheduledMaskFactor ρ₁ E K I₁ a P) (reachedScheduledMaskFactor ρ₂ E K I₂ a Q)
  · exact fun x hx w ↦ scheduledMaskProduct_eq_reached_mul ρ₁ E K I₁ a hP hx w
  · exact fun y hy w ↦ scheduledMaskProduct_eq_reached_mul ρ₂ E K I₂ a hQ hy w
  · intro w
    rw [abs_of_nonneg (reachedScheduledMaskFactor_mem_Icc ρ₁ E K I₁ a P w).1]
    exact (reachedScheduledMaskFactor_mem_Icc ρ₁ E K I₁ a P w).2
  · intro w
    rw [abs_of_nonneg (reachedScheduledMaskFactor_mem_Icc ρ₂ E K I₂ a Q w).1]
    exact (reachedScheduledMaskFactor_mem_Icc ρ₂ E K I₂ a Q w).2

end FalconerThetaGauge
