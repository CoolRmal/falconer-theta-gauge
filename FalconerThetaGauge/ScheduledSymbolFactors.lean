module

public import FalconerThetaGauge.ScheduledSymbolDerivatives

/-! # Actual Borel normalized derivative factors on the occupied anchor partition -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

open GaugeFrostman

def normalizedScheduledTestSymbol (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K k : ℕ) : Plane → UnitCircle → ℝ :=
  partitionDirectionalSymbol (occupiedUnitCells ρ test.anchor) (dyadicCube test.anchor)
    (fun P ↦ normalizedCircleMaskDerivative K k (scheduledMaskScale E test)
      (scheduledPassingDirections ρ E width test P))

theorem measurable_normalizedScheduledTestSymbol (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K k : ℕ) :
    Measurable (uncurry (normalizedScheduledTestSymbol ρ E width test K k)) :=
  measurable_partitionDirectionalSymbol (fun P _ ↦ measurableSet_dyadicCube test.anchor P)
    (fun _ _ ↦ measurable_normalizedCircleMaskDerivative K k (scheduledMaskScale_pos E test) _)

theorem normalizedScheduledTestSymbol_eq_on_cell (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K k : ℕ) {P : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ test.anchor) {x : Plane}
    (hx : x ∈ dyadicCube test.anchor P) (w : UnitCircle) :
    normalizedScheduledTestSymbol ρ E width test K k x w =
      normalizedCircleMaskDerivative K k (scheduledMaskScale E test)
        (scheduledPassingDirections ρ E width test P) w :=
  partitionDirectionalSymbol_eq_on_cell (occupiedUnitCells_pairwiseDisjoint ρ test.anchor)
    _ hP hx w

theorem normalizedScheduledTestSymbol_zero (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) (x : Plane) (w : UnitCircle) :
    normalizedScheduledTestSymbol ρ E width test K 0 x w =
      scheduledWidthTestSymbol ρ E width test K x w := by
  unfold normalizedScheduledTestSymbol scheduledWidthTestSymbol partitionCirclePassingSymbol
    partitionDirectionalSymbol
  simp only [normalizedCircleMaskDerivative_zero]

theorem norm_normalizedScheduledTestSymbol_le_one (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K k : ℕ) (hk : k ≤ K) (x : Plane) (w : UnitCircle) :
    ‖normalizedScheduledTestSymbol ρ E width test K k x w‖ ≤ 1 := by
  by_cases hx : ∃ P ∈ occupiedUnitCells ρ test.anchor, x ∈ dyadicCube test.anchor P
  · obtain ⟨P, hP, hxP⟩ := hx
    rw [normalizedScheduledTestSymbol_eq_on_cell ρ E width test K k hP hxP]
    exact norm_normalizedCircleMaskDerivative_le_one K k hk (scheduledMaskScale_pos E test) _ w
  · rw [normalizedScheduledTestSymbol, partitionDirectionalSymbol_eq_zero_off_cells _ _ _
      (by simpa only [not_exists, not_and] using hx)]
    simp

theorem contDiff_normalizedScheduledTestSymbol_comp_angle (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K k : ℕ) (x : Plane) :
    ContDiff ℝ ∞
      (fun θ ↦ normalizedScheduledTestSymbol ρ E width test K k x (unitCircleOfAngle θ)) := by
  unfold normalizedScheduledTestSymbol partitionDirectionalSymbol
  apply ContDiff.sum
  intro P hP
  by_cases hx : x ∈ dyadicCube test.anchor P
  · simp only [indicator_of_mem hx]
    exact contDiff_normalizedCircleMaskDerivative_comp_angle K k
      (scheduledMaskScale_pos E test) _
  · simp only [indicator_of_notMem hx]
    exact contDiff_const

def scheduledSymbolDerivativeCoefficient (E : ℝ) (test : ProfileScheduleTest) (k : ℕ) : ℝ :=
  (scheduledMaskScale E test)⁻¹ * (Real.pi ^ 2 / 6) * ((k + 1 : ℕ) : ℝ) ^ 2

theorem scheduledSymbolDerivativeCoefficient_nonneg (E : ℝ) (test : ProfileScheduleTest)
    (k : ℕ) : 0 ≤ scheduledSymbolDerivativeCoefficient E test k := by
  unfold scheduledSymbolDerivativeCoefficient
  have hs := scheduledMaskScale_pos E test
  positivity

theorem deriv_normalizedScheduledTestSymbol_comp_angle (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (K k : ℕ) (x : Plane) (θ : ℝ) :
    deriv (fun t ↦ normalizedScheduledTestSymbol ρ E width test K k x
      (unitCircleOfAngle t)) θ = scheduledSymbolDerivativeCoefficient E test k *
        normalizedScheduledTestSymbol ρ E width test K (k + 1) x (unitCircleOfAngle θ) := by
  by_cases hx : ∃ P ∈ occupiedUnitCells ρ test.anchor, x ∈ dyadicCube test.anchor P
  · obtain ⟨P, hP, hxP⟩ := hx
    simp_rw [normalizedScheduledTestSymbol_eq_on_cell ρ E width test K _ hP hxP]
    exact deriv_normalizedCircleMaskDerivative_comp_angle K k (scheduledMaskScale_pos E test) _ θ
  · have heq : ∀ j, (fun t ↦ normalizedScheduledTestSymbol ρ E width test K j x
        (unitCircleOfAngle t)) = fun _ : ℝ ↦ 0 := by
      intro j
      ext t
      exact partitionDirectionalSymbol_eq_zero_off_cells _ _ _
        (by simpa only [not_exists, not_and] using hx) _
    rw [heq k]
    change _ = scheduledSymbolDerivativeCoefficient E test k *
      (fun t ↦ normalizedScheduledTestSymbol ρ E width test K (k + 1) x
        (unitCircleOfAngle t)) θ
    rw [heq (k + 1)]
    simp

/-- S4 for every literal normalized derivative factor on a finer occupied cell. -/
theorem normalizedScheduledTestSymbol_eq_ancestor (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E width : ℝ) (test : ProfileScheduleTest) (K k : ℕ) {a : ℕ} (ha : test.anchor ≤ a)
    {P : Fin 2 → ℤ} (hP : P ∈ occupiedUnitCells ρ a) {x : Plane}
    (hx : x ∈ dyadicCube a P) (w : UnitCircle) :
    normalizedScheduledTestSymbol ρ E width test K k x w =
      normalizedCircleMaskDerivative K k (scheduledMaskScale E test)
        (scheduledPassingDirections ρ E width test (ancestor (a - test.anchor) P)) w :=
  normalizedScheduledTestSymbol_eq_on_cell ρ E width test K k
    (occupiedUnitCells_ancestor_of_le ρ ha hP) (mem_dyadicCube_ancestor_of_mem ha hx) w

end FalconerThetaGauge
