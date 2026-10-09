/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationOperatorIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The genuine countable Fourier expansion of each polynomial inverse operator -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem hasSum_finite_complex_prod {ι : Type*} [Fintype ι]
    (f : ι → ℕ → ℂ) (g : ι → ℂ) (hf : ∀ b, HasSum (f b) (g b)) :
    HasSum (fun z : ι × ℕ ↦ f z.1 z.2) (∑ b, g b) := by
  have hn : Summable (fun z : ι × ℕ ↦ ‖f z.1 z.2‖) :=
    (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
      ⟨fun b ↦ (hf b).summable.norm, Summable.of_finite⟩
  have h := hn.of_norm
  convert h.hasSum using 1
  rw [h.tsum_prod' (fun b ↦ (hf b).summable), tsum_fintype]
  apply sum_congr rfl
  intro b _
  exact (hf b).tsum_eq.symm

def scheduledPairSeparatedCoefficient (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (x₀ y₀ : Plane) (ρ : ℝ) (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) : ℂ :=
  scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ z.1 *
    (spatialInversePowerSequenceCoefficient j x₀ y₀ ρ z.2 : ℂ)

def scheduledPairSeparatedLeftSymbol (p : Polynomial ℂ) (d : ScheduledSymbolData)
    (ρ₁ : Measure Plane) (X : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (x₀ : Plane) (ρ : ℝ)
    (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) : Plane → UnitCircle → ℝ :=
  carrierPolynomialSymbol X (spatialInversePowerSequenceLeftPolynomial x₀ ρ z.2)
    ((scheduledPairOperatorLeftData p d I₁ I₂ z.1).symbol ρ₁ E width K I₁)

def scheduledPairSeparatedRightSymbol (p : Polynomial ℂ) (d : ScheduledSymbolData)
    (ρ₂ : Measure Plane) (Y : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (y₀ : Plane) (ρ : ℝ)
    (z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ) : Plane → UnitCircle → ℝ :=
  carrierPolynomialSymbol Y (spatialInversePowerSequenceRightPolynomial y₀ ρ z.2)
    ((scheduledPairOperatorRightData p d I₁ I₂ z.1).symbol ρ₂ E width K I₂)

theorem scheduledPairOperatorPairing_hasSum (p : Polynomial ℂ) (j : ℕ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + p.natDegree ≤ K)
    (horder₂ : d₂.order I₂ + p.natDegree ≤ K)
    {ψ : UnitCircle → ℝ} (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    HasSum (fun z : ScheduledPairOperatorBranch p I₁ I₂ × ℕ ↦
      scheduledPairSeparatedCoefficient p j d₁ d₂ E I₁ I₂ x₀ y₀ ρ z *
        maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y
          (scheduledPairSeparatedLeftSymbol p d₁ ρ₁ X E width K I₁ I₂ x₀ ρ z)
          (scheduledPairSeparatedRightSymbol p d₂ ρ₂ Y E width K I₁ I₂ y₀ ρ z) ψ r)
      (scheduledPairOperatorPairing p j d₁ d₂ ρ₁ ρ₂ X Y E width K I₁ I₂ ψ r) := by
  have hf (b : ScheduledPairOperatorBranch p I₁ I₂) :=
    (separated_inversePower_bilinear_hasSum j ρ₁ ρ₂ hρ hsep hX hY hXball hYball
      ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).measurable_symbol ρ₁ E width K I₁)
      ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).measurable_symbol ρ₂ E width K I₂)
      ((scheduledPairOperatorLeftData p d₁ I₁ I₂ b).abs_symbol_le_one ρ₁ E width K I₁
        ((scheduledPairOperatorLeftData_order_le p d₁ I₁ I₂ b).trans horder₁))
      ((scheduledPairOperatorRightData p d₂ I₁ I₂ b).abs_symbol_le_one ρ₂ E width K I₂
        ((scheduledPairOperatorRightData_order_le p d₂ I₁ I₂ b).trans horder₂))
      hψ hψ₁ r).mul_left
      (scheduledPairOperatorBranchCoefficient p d₁ d₂ E I₁ I₂ b)
  rw [scheduledPairOperatorPairing_eq_finite p j d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY hXball hYball
    E width K I₁ I₂ horder₁ horder₂ hψ hψ₁ r]
  simpa only [scheduledPairSeparatedCoefficient, scheduledPairSeparatedLeftSymbol,
    scheduledPairSeparatedRightSymbol, mul_assoc] using hasSum_finite_complex_prod _ _ hf

end FalconerThetaGauge
