/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationIntegral

/-! # The literal normalized bilinear Fourier expansion in Step 2 of Estimate 7.5 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

theorem separated_inversePower_bilinear_hasSum (j : ℕ)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    HasSum (fun n ↦ (spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n : ℂ) *
      maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y
        (carrierPolynomialSymbol X (spatialInversePowerSequenceLeftPolynomial x₀ ρ n) b₁)
        (carrierPolynomialSymbol Y (spatialInversePowerSequenceRightPolynomial y₀ ρ n) b₂)
        ψ r)
      ((Real.sqrt r : ℂ) * ∫ p, ((dist p.1 p.2)⁻¹ ^ j : ℝ) *
        (∫ w, (ψ w : ℂ) * maskedFourierPairKernel b₁ b₂ r w p ∂circleArcLength)
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  have h := (separated_inversePower_circleIntegral_hasSum j ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁ r).mul_left (Real.sqrt r : ℂ)
  simpa only [maskedFourierBilinearAmplitude, mul_assoc, mul_comm, mul_left_comm] using h

theorem separation_left_symbol_mem_class {x₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    {X : Set Plane} (hX : MeasurableSet X) (hXball : X ⊆ closedBall x₀ ρ)
    (ρ₁ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (k₀ : ℕ)
    {b : Plane → UnitCircle → ℝ} (hb : b ∈ scheduledSymbolClass ρ₁ E width K I k₀)
    (n : ℕ) :
    carrierPolynomialSymbol X (spatialInversePowerSequenceLeftPolynomial x₀ ρ n) b ∈
      scheduledSymbolClass ρ₁ E width K I k₀ :=
  carrierPolynomialSymbol_mem_scheduledSymbolClass hX _
    (fun _x hx ↦ abs_eval_spatialInversePowerSequenceLeftPolynomial_le_one hρ (hXball hx) n)
    ρ₁ E width K I k₀ hb

theorem separation_right_symbol_mem_class {y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    {Y : Set Plane} (hY : MeasurableSet Y) (hYball : Y ⊆ closedBall y₀ ρ)
    (ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (k₀ : ℕ)
    {b : Plane → UnitCircle → ℝ} (hb : b ∈ scheduledSymbolClass ρ₂ E width K I k₀)
    (n : ℕ) :
    carrierPolynomialSymbol Y (spatialInversePowerSequenceRightPolynomial y₀ ρ n) b ∈
      scheduledSymbolClass ρ₂ E width K I k₀ :=
  carrierPolynomialSymbol_mem_scheduledSymbolClass hY _
    (fun _y hy ↦ abs_eval_spatialInversePowerSequenceRightPolynomial_le_one hρ (hYball hy) n)
    ρ₂ E width K I k₀ hb

end FalconerThetaGauge
