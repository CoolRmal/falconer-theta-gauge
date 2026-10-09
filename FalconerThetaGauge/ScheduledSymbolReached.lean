module

public import FalconerThetaGauge.ScheduledSymbolAssembly

/-! # S4 and removal of reached derivative factors in actual built-symbol Fourier energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

open GaugeFrostman

theorem ScheduledSymbolData.order_le_of_subset (d : ScheduledSymbolData)
    {I J : Finset ProfileScheduleTest} (hIJ : I ⊆ J) : d.order I ≤ d.order J :=
  Finset.sum_le_sum_of_subset hIJ

def ScheduledSymbolData.reachedFactor (d : ScheduledSymbolData) (ρ : Measure Plane)
    (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (a : ℕ) (P : Fin 2 → ℤ) :
    UnitCircle → ℝ :=
  fun w ↦ ∏ test ∈ I.filter (fun test ↦ test.anchor ≤ a),
    normalizedCircleMaskDerivative K (d.derivativeOrders test) (scheduledMaskScale E test)
      (scheduledPassingDirections ρ E width test (ancestor (a - test.anchor) P)) w

theorem ScheduledSymbolData.abs_reachedFactor_le_one (d : ScheduledSymbolData)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest)
    (horder : d.order I ≤ K) (a : ℕ) (P : Fin 2 → ℤ) (w : UnitCircle) :
    |d.reachedFactor ρ E width K I a P w| ≤ 1 := by
  rw [ScheduledSymbolData.reachedFactor, Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _)
  intro test ht
  simpa only [Real.norm_eq_abs] using norm_normalizedCircleMaskDerivative_le_one K
    (d.derivativeOrders test)
    ((d.derivativeOrders_le_order I (Finset.mem_filter.1 ht).1).trans horder)
    (scheduledMaskScale_pos E test) _ w

/-- The exact product factorization removes all reached derivatives,
retaining the spatial weight. -/
theorem ScheduledSymbolData.symbol_eq_reached_mul (d : ScheduledSymbolData)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (a : ℕ) {P : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ a) {x : Plane} (hx : x ∈ dyadicCube a P) (w : UnitCircle) :
    d.symbol ρ E width K I x w = d.reachedFactor ρ E width K I a P w *
      d.symbol ρ E width K (I.filter (fun test ↦ a < test.anchor)) x w := by
  rw [ScheduledSymbolData.symbol, ← Finset.prod_filter_mul_prod_filter_not I
    (fun test ↦ test.anchor ≤ a)]
  have heq : (∏ test ∈ I.filter (fun test ↦ test.anchor ≤ a),
      normalizedScheduledTestSymbol ρ E width test K (d.derivativeOrders test) x w) =
      d.reachedFactor ρ E width K I a P w := by
    apply Finset.prod_congr rfl
    intro test ht
    exact normalizedScheduledTestSymbol_eq_ancestor ρ E width test K _
      (Finset.mem_filter.1 ht).2 hP hx w
  rw [heq]
  simp only [not_le, ScheduledSymbolData.symbol]
  ring

/-- Removing reached factors is valid for every symbol in the actual order-bounded class. -/
theorem maskedFourierEnergy_builtSymbol_drop_reached (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ ≤ K) (horder₂ : d₂.order I₂ ≤ K) (a : ℕ) {P Q : Fin 2 → ℤ}
    (hP : P ∈ occupiedUnitCells ρ₁ a) (hQ : Q ∈ occupiedUnitCells ρ₂ a) (cutoffK v : ℕ) :
    maskedFourierEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
        (d₁.symbol ρ₁ E width K I₁) (d₂.symbol ρ₂ E width K I₂) cutoffK v ≤
      maskedFourierEnergy ρ₁ ρ₂ (dyadicCube a P) (dyadicCube a Q)
        (d₁.symbol ρ₁ E width K (I₁.filter (fun test ↦ a < test.anchor)))
        (d₂.symbol ρ₂ E width K (I₂.filter (fun test ↦ a < test.anchor))) cutoffK v := by
  have ho₁ := (d₁.order_le_of_subset
    (Finset.filter_subset (fun test ↦ a < test.anchor) I₁)).trans horder₁
  have ho₂ := (d₂.order_le_of_subset
    (Finset.filter_subset (fun test ↦ a < test.anchor) I₂)).trans horder₂
  apply maskedFourierEnergy_le_of_eqOn ρ₁ ρ₂
    (measurableSet_dyadicCube a P) (measurableSet_dyadicCube a Q)
    (d₁.measurable_symbol ρ₁ E width K _) (d₂.measurable_symbol ρ₂ E width K _)
    (d₁.measurable_symbol ρ₁ E width K _) (d₂.measurable_symbol ρ₂ E width K _)
    (d₁.abs_symbol_le_one ρ₁ E width K _ ho₁)
    (d₂.abs_symbol_le_one ρ₂ E width K _ ho₂)
    (d₁.abs_symbol_le_one ρ₁ E width K _ horder₁)
    (d₂.abs_symbol_le_one ρ₂ E width K _ horder₂)
    (d₁.reachedFactor ρ₁ E width K I₁ a P) (d₂.reachedFactor ρ₂ E width K I₂ a Q)
  · exact fun x hx w ↦ d₁.symbol_eq_reached_mul ρ₁ E width K I₁ a hP hx w
  · exact fun y hy w ↦ d₂.symbol_eq_reached_mul ρ₂ E width K I₂ a hQ hy w
  · exact d₁.abs_reachedFactor_le_one ρ₁ E width K I₁ horder₁ a P
  · exact d₂.abs_reachedFactor_le_one ρ₂ E width K I₂ horder₂ a Q

end FalconerThetaGauge
