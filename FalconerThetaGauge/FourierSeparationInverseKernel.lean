/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationOperatorSeriesBudget
public import FalconerThetaGauge.MaskedMattilaCircleKernel

/-! # Literal prepared inverse circle kernels and their separated Fourier expansion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial
open scoped Classical ContDiff RealInnerProductSpace

namespace FalconerThetaGauge

theorem scheduledPairOperatorPairing_inverse_eq (j T : ℕ) (α : ℝ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + (stationaryPhaseInversePolynomial j).natDegree ≤ K)
    (horder₂ : d₂.order I₂ + (stationaryPhaseInversePolynomial j).natDegree ≤ K) (r : ℝ) :
    scheduledPairOperatorPairing (stationaryPhaseInversePolynomial j) j d₁ d₂
      ρ₁ ρ₂ X Y E width K I₁ I₂ (preparedArcCutoff (6 * T) α) r =
      (Real.sqrt r : ℂ) * ∫ z, ((dist z.1 z.2)⁻¹ ^ j : ℝ) *
        preparedInverseCircleKernelIntegral T α
          (builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
            (d₂.symbol ρ₂ E width K I₂) z.1 z.2) (z.1 - z.2) r j
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) := by
  have hψ₁ : ∀ w, |preparedArcCutoff (6 * T) α w| ≤ 1 := fun w ↦
    (abs_le.mpr ⟨by linarith [(preparedArcCutoff_mem_Icc (6 * T) α w).1],
      (preparedArcCutoff_mem_Icc (6 * T) α w).2⟩)
  have hi := integrable_scheduledPairOperatorCircleKernel
    (stationaryPhaseInversePolynomial j) j d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY hXball hYball
      E width K I₁ I₂ horder₁ horder₂ (measurable_preparedArcCutoff _ _) hψ₁ r
  rw [scheduledPairOperatorPairing, integral_prod_symm _ hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [preparedInverseCircleKernelIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have hB : builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
      (d₂.symbol ρ₂ E width K I₂) z.1 z.2 = fun t ↦
        (d₁.symbol ρ₁ E width K I₁ z.1 (unitCircleOfAngle t) : ℂ) *
        (d₂.symbol ρ₂ E width K I₂ z.2 (unitCircleOfAngle t) : ℂ) := by
    funext t
    rfl
  simp only [scheduledPairOperatorCircleKernel, preparedInverseCircleAmplitude,
    stationaryPhaseInverseOperator, hB]
  ring

theorem preparedInverseCircle_spatial_hasSum (j T : ℕ) (α : ℝ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + (stationaryPhaseInversePolynomial j).natDegree ≤ K)
    (horder₂ : d₂.order I₂ + (stationaryPhaseInversePolynomial j).natDegree ≤ K) (r : ℝ) :
    HasSum (fun z :
      ScheduledPairOperatorBranch (stationaryPhaseInversePolynomial j) I₁ I₂ × ℕ ↦
      scheduledPairSeparatedCoefficient (stationaryPhaseInversePolynomial j) j
        d₁ d₂ E I₁ I₂ x₀ y₀ ρ z * maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y
          (scheduledPairSeparatedLeftSymbol (stationaryPhaseInversePolynomial j)
            d₁ ρ₁ X E width K I₁ I₂ x₀ ρ z)
          (scheduledPairSeparatedRightSymbol (stationaryPhaseInversePolynomial j)
            d₂ ρ₂ Y E width K I₁ I₂ y₀ ρ z) (preparedArcCutoff (6 * T) α) r)
      ((Real.sqrt r : ℂ) * ∫ z, ((dist z.1 z.2)⁻¹ ^ j : ℝ) *
        preparedInverseCircleKernelIntegral T α
          (builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
            (d₂.symbol ρ₂ E width K I₂) z.1 z.2) (z.1 - z.2) r j
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  rw [← scheduledPairOperatorPairing_inverse_eq j T α d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball E width K I₁ I₂ horder₁ horder₂ r]
  exact scheduledPairOperatorPairing_hasSum (stationaryPhaseInversePolynomial j) j d₁ d₂
    ρ₁ ρ₂ hρ hsep hX hY hXball hYball E width K I₁ I₂ horder₁ horder₂
    (measurable_preparedArcCutoff _ _) (fun w ↦ abs_le.mpr
      ⟨by linarith [(preparedArcCutoff_mem_Icc (6 * T) α w).1],
        (preparedArcCutoff_mem_Icc (6 * T) α w).2⟩) r

end FalconerThetaGauge
