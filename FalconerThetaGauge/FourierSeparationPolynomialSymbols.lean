/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationKernel
public import FalconerThetaGauge.SpatialInversePowerSequence
public import FalconerThetaGauge.ScheduledSymbolClass
public import Mathlib.Topology.Algebra.MvPolynomial

/-! # Actual bounded carrier polynomial factors preserve the built symbol class -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

def carrierPolynomialWeight (X : Set Plane) (p : MvPolynomial (Fin 2) ℝ) : Plane → ℝ :=
  X.indicator (fun x ↦ MvPolynomial.eval (fun i ↦ x i) p)

def carrierPolynomialSymbol (X : Set Plane) (p : MvPolynomial (Fin 2) ℝ)
    (b : Plane → UnitCircle → ℝ) : Plane → UnitCircle → ℝ :=
  fun x w ↦ carrierPolynomialWeight X p x * b x w

theorem measurable_carrierPolynomialWeight {X : Set Plane} (hX : MeasurableSet X)
    (p : MvPolynomial (Fin 2) ℝ) : Measurable (carrierPolynomialWeight X p) := by
  have hc : Continuous (fun x : Plane ↦ MvPolynomial.eval (fun i ↦ x i) p) :=
    p.continuous_eval.comp (by fun_prop)
  exact hc.measurable.indicator hX

theorem abs_carrierPolynomialWeight_le_one {X : Set Plane} (p : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ x ∈ X, |MvPolynomial.eval (fun i ↦ x i) p| ≤ 1) (x : Plane) :
    |carrierPolynomialWeight X p x| ≤ 1 := by
  by_cases hx : x ∈ X
  · simpa only [carrierPolynomialWeight, indicator_of_mem hx] using hp x hx
  · simp [carrierPolynomialWeight, hx]

@[fun_prop]
theorem measurable_carrierPolynomialSymbol {X : Set Plane} (hX : MeasurableSet X)
    (p : MvPolynomial (Fin 2) ℝ) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) : Measurable (uncurry (carrierPolynomialSymbol X p b)) :=
  ((measurable_carrierPolynomialWeight hX p).comp measurable_fst).mul hb

theorem abs_carrierPolynomialSymbol_le_one {X : Set Plane} (p : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ x ∈ X, |MvPolynomial.eval (fun i ↦ x i) p| ≤ 1)
    {b : Plane → UnitCircle → ℝ} (hb : ∀ x w, |b x w| ≤ 1) (x : Plane) (w : UnitCircle) :
    |carrierPolynomialSymbol X p b x w| ≤ 1 := by
  rw [carrierPolynomialSymbol, abs_mul]
  exact (mul_le_mul (abs_carrierPolynomialWeight_le_one p hp x) (hb x w)
    (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem carrierPolynomialSymbol_eq_on_carrier {X : Set Plane}
    (p : MvPolynomial (Fin 2) ℝ) (b : Plane → UnitCircle → ℝ) {x : Plane}
    (hx : x ∈ X) (w : UnitCircle) :
    carrierPolynomialSymbol X p b x w = MvPolynomial.eval (fun i ↦ x i) p * b x w := by
  simp only [carrierPolynomialSymbol, carrierPolynomialWeight, indicator_of_mem hx]

def ScheduledSymbolData.withCarrierPolynomial (d : ScheduledSymbolData) {X : Set Plane}
    (hX : MeasurableSet X) (p : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ x ∈ X, |MvPolynomial.eval (fun i ↦ x i) p| ≤ 1) : ScheduledSymbolData where
  spatialWeight := fun x ↦ carrierPolynomialWeight X p x * d.spatialWeight x
  derivativeOrders := d.derivativeOrders
  measurable_spatialWeight := (measurable_carrierPolynomialWeight hX p).mul
    d.measurable_spatialWeight
  abs_spatialWeight_le_one := by
    intro x
    rw [abs_mul]
    exact (mul_le_mul (abs_carrierPolynomialWeight_le_one p hp x)
      (d.abs_spatialWeight_le_one x) (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem ScheduledSymbolData.withCarrierPolynomial_order (d : ScheduledSymbolData)
    {X : Set Plane} (hX : MeasurableSet X) (p : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ x ∈ X, |MvPolynomial.eval (fun i ↦ x i) p| ≤ 1)
    (I : Finset ProfileScheduleTest) : (d.withCarrierPolynomial hX p hp).order I = d.order I :=
  rfl

theorem ScheduledSymbolData.withCarrierPolynomial_symbol (d : ScheduledSymbolData)
    {X : Set Plane} (hX : MeasurableSet X) (p : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ x ∈ X, |MvPolynomial.eval (fun i ↦ x i) p| ≤ 1)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) :
    (d.withCarrierPolynomial hX p hp).symbol ρ E width K I =
      carrierPolynomialSymbol X p (d.symbol ρ E width K I) := by
  funext x w
  simp only [ScheduledSymbolData.symbol, ScheduledSymbolData.withCarrierPolynomial,
    carrierPolynomialSymbol]
  ring

theorem carrierPolynomialSymbol_mem_scheduledSymbolClass {X : Set Plane}
    (hX : MeasurableSet X) (p : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ x ∈ X, |MvPolynomial.eval (fun i ↦ x i) p| ≤ 1)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (k₀ : ℕ)
    {b : Plane → UnitCircle → ℝ} (hb : b ∈ scheduledSymbolClass ρ E width K I k₀) :
    carrierPolynomialSymbol X p b ∈ scheduledSymbolClass ρ E width K I k₀ := by
  obtain ⟨d, hd, rfl⟩ := hb
  refine ⟨d.withCarrierPolynomial hX p hp, hd, ?_⟩
  exact (d.withCarrierPolynomial_symbol hX p hp ρ E width K I).symm

end FalconerThetaGauge
