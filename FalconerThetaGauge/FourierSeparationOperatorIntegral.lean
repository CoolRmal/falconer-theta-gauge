/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationOperatorBranches
public import FalconerThetaGauge.FourierSeparationIntegrability

/-! # The actual polynomial operator under both spatial and angular integrals -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial
open scoped Classical ContDiff RealInnerProductSpace

namespace FalconerThetaGauge

def scheduledPairOperatorCircleKernel (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (ρ₁ ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (ψ : UnitCircle → ℝ) (r : ℝ)
    (z : UnitCircle × (Plane × Plane)) : ℂ :=
  (((dist z.2.1 z.2.2)⁻¹ ^ j : ℝ) : ℂ) * (ψ z.1 : ℂ) *
    Complex.exp (-((r * inner ℝ (z.2.1 - z.2.2) (z.1 : Plane) : ℝ) : ℂ) * Complex.I) *
    polynomialDifferentialAction p
      (fun t ↦ (d₁.symbol ρ₁ E width K I₁ z.2.1 (unitCircleOfAngle t) : ℂ) *
        (d₂.symbol ρ₂ E width K I₂ z.2.2 (unitCircleOfAngle t) : ℂ)) (circleAngle z.1)

def scheduledPairOperatorPairing (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (ψ : UnitCircle → ℝ) (r : ℝ) : ℂ :=
  (Real.sqrt r : ℂ) * ∫ z, scheduledPairOperatorCircleKernel
    p j d₁ d₂ ρ₁ ρ₂ E width K I₁ I₂ ψ r z
      ∂circleArcLength.prod ((ρ₁.restrict X).prod (ρ₂.restrict Y))

theorem scheduledPairOperatorCircleKernel_eq (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (ρ₁ ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (ψ : UnitCircle → ℝ) (r : ℝ)
    (z : UnitCircle × (Plane × Plane)) :
    scheduledPairOperatorCircleKernel p j d₁ d₂ ρ₁ ρ₂ E width K I₁ I₂ ψ r z =
      ∑ b : ScheduledPairOperatorBranch p I₁ I₂,
        scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b *
          inversePowerCircleKernel j
            ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).symbol ρ₁ E width K I₁)
            ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).symbol
              ρ₂ E width K I₂) ψ r z := by
  simp only [scheduledPairOperatorCircleKernel,
    polynomialDifferentialAction_scheduledPairOperator_eq,
    unitCircleOfAngle_circleAngle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [inversePowerCircleKernel, maskedFourierPairKernel]
  ring

theorem integrable_scheduledPairOperatorCircleKernel (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + p.natDegree ≤ K)
    (horder₂ : d₂.order I₂ + p.natDegree ≤ K)
    {ψ : UnitCircle → ℝ} (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    Integrable (scheduledPairOperatorCircleKernel
      p j d₁ d₂ ρ₁ ρ₂ E width K I₁ I₂ ψ r)
      (circleArcLength.prod ((ρ₁.restrict X).prod (ρ₂.restrict Y))) := by
  have hi (b : ScheduledPairOperatorBranch p I₁ I₂) :=
    integrable_inversePowerCircleKernel j ρ₁ ρ₂ hρ hsep hX hY hXball hYball
      ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).measurable_symbol ρ₁ E width K I₁)
      ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).measurable_symbol ρ₂ E width K I₂)
      ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).abs_symbol_le_one ρ₁ E width K I₁
        ((scheduledPairOperatorLeftData_order_le p d₁ I₁ I₂ b).trans horder₁))
      ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).abs_symbol_le_one ρ₂ E width K I₂
        ((scheduledPairOperatorRightData_order_le p d₂ I₁ I₂ b).trans horder₂)) hψ hψ₁ r
  apply (integrable_finsetSum Finset.univ (fun b _ ↦
    (hi b).const_mul (scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b))).congr
  exact Eventually.of_forall (fun z ↦
    (scheduledPairOperatorCircleKernel_eq
      p j d₁ d₂ ρ₁ ρ₂ E width K I₁ I₂ ψ r z).symm)

theorem scheduledPairOperatorPairing_eq_finite (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + p.natDegree ≤ K)
    (horder₂ : d₂.order I₂ + p.natDegree ≤ K)
    {ψ : UnitCircle → ℝ} (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    scheduledPairOperatorPairing p j d₁ d₂ ρ₁ ρ₂ X Y E width K I₁ I₂ ψ r =
      ∑ b : ScheduledPairOperatorBranch p I₁ I₂,
        scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b *
          ((Real.sqrt r : ℂ) * ∫ z, ((dist z.1 z.2)⁻¹ ^ j : ℝ) *
            (∫ w, (ψ w : ℂ) * maskedFourierPairKernel
              ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).symbol ρ₁ E width K I₁)
              ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).symbol ρ₂ E width K I₂)
              r w z ∂circleArcLength) ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  have hi (b : ScheduledPairOperatorBranch p I₁ I₂) :=
    integrable_inversePowerCircleKernel j ρ₁ ρ₂ hρ hsep hX hY hXball hYball
      ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).measurable_symbol ρ₁ E width K I₁)
      ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).measurable_symbol ρ₂ E width K I₂)
      ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).abs_symbol_le_one ρ₁ E width K I₁
        ((scheduledPairOperatorLeftData_order_le p d₁ I₁ I₂ b).trans horder₁))
      ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).abs_symbol_le_one ρ₂ E width K I₂
        ((scheduledPairOperatorRightData_order_le p d₂ I₁ I₂ b).trans horder₂)) hψ hψ₁ r
  simp only [scheduledPairOperatorPairing, scheduledPairOperatorCircleKernel_eq]
  rw [integral_finsetSum _ (fun b _ ↦ (hi b).const_mul _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul, integral_inversePowerCircleKernel_eq j ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball
    ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).measurable_symbol ρ₁ E width K I₁)
    ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).measurable_symbol ρ₂ E width K I₂)
    ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).abs_symbol_le_one ρ₁ E width K I₁
      ((scheduledPairOperatorLeftData_order_le p d₁ I₁ I₂ b).trans horder₁))
    ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).abs_symbol_le_one ρ₂ E width K I₂
      ((scheduledPairOperatorRightData_order_le p d₂ I₁ I₂ b).trans horder₂)) hψ hψ₁ r]
  ring

end FalconerThetaGauge
