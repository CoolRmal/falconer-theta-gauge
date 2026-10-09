module

public import FalconerThetaGauge.ScheduledSymbolClass

/-! # Nonzero built symbols lie on the actual occupied anchor carrier -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem ScheduledSymbolData.ne_zero_implies_anchorCarrier (d : ScheduledSymbolData)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest)
    {x : Plane} {w : UnitCircle} (hb : d.symbol ρ E width K I x w ≠ 0) :
    x ∈ scheduledAnchorCarrier ρ I := by
  apply mem_iInter₂.mpr
  intro test ht
  have hf := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hb).2) test ht
  by_contra hx
  have hoff : ∀ P ∈ occupiedUnitCells ρ test.anchor,
      x ∉ dyadicCube test.anchor P := by
    intro P hP hxP
    exact hx (mem_iUnion₂.mpr ⟨P, hP, hxP⟩)
  have hz := partitionDirectionalSymbol_eq_zero_off_cells
    (occupiedUnitCells ρ test.anchor) (dyadicCube test.anchor)
    (fun P ↦ normalizedCircleMaskDerivative K (d.derivativeOrders test)
      (scheduledMaskScale E test) (scheduledPassingDirections ρ E width test P)) hoff w
  exact hf hz

theorem ne_zero_implies_next_passing_of_mem_scheduledSymbolClass (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (E : ℝ) {L : ℕ} (hL : 0 < L)
    (hsize : (L : ℝ) ≤ (2 : ℝ) ^ E / 8) (i K k₀ : ℕ)
    (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth L i) K I k₀)
    {x : Plane} {w : UnitCircle} (hbx : b x w ≠ 0) :
    ∀ test ∈ I, (x, w) ∈ scheduledPassingPinSet ρ E
      (directionalLevelWidth L (i + 1)) test := by
  obtain ⟨d, _, rfl⟩ := hb
  exact d.ne_zero_implies_next_passing ρ E hL hsize i K I hordered
    (d.ne_zero_implies_anchorCarrier ρ E _ K I hbx) w hbx

end FalconerThetaGauge
