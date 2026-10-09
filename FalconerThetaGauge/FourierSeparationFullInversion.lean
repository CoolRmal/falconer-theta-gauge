/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationFrequencyBudget

/-! # Exact spatial integration of the full prepared inverse circle series -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff RealInnerProductSpace

namespace FalconerThetaGauge

theorem integral_scheduledPairOperator_inverse_circle_eq (j T : ℕ) (α : ℝ)
    (d₁ d₂ : ScheduledSymbolData) (ρ₁ ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (r : ℝ) (z : Plane × Plane) :
    (∫ w, scheduledPairOperatorCircleKernel (stationaryPhaseInversePolynomial j) j
      d₁ d₂ ρ₁ ρ₂ E width K I₁ I₂ (preparedArcCutoff (6 * T) α) r (w, z)
        ∂circleArcLength) = ((dist z.1 z.2)⁻¹ ^ j : ℝ) *
      preparedInverseCircleKernelIntegral T α
        (builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
          (d₂.symbol ρ₂ E width K I₂) z.1 z.2) (z.1 - z.2) r j := by
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

theorem integrable_spatial_preparedInverseCircleKernel (j T : ℕ) (α : ℝ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + (stationaryPhaseInversePolynomial j).natDegree ≤ K)
    (horder₂ : d₂.order I₂ + (stationaryPhaseInversePolynomial j).natDegree ≤ K) (r : ℝ) :
    Integrable (fun z : Plane × Plane ↦ ((dist z.1 z.2)⁻¹ ^ j : ℝ) *
      preparedInverseCircleKernelIntegral T α
        (builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
          (d₂.symbol ρ₂ E width K I₂) z.1 z.2) (z.1 - z.2) r j)
        ((ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  have hi := integrable_scheduledPairOperatorCircleKernel
    (stationaryPhaseInversePolynomial j) j d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY hXball hYball
      E width K I₁ I₂ horder₁ horder₂ (measurable_preparedArcCutoff _ _)
      (fun w ↦ abs_le.mpr ⟨by linarith [(preparedArcCutoff_mem_Icc (6 * T) α w).1],
        (preparedArcCutoff_mem_Icc (6 * T) α w).2⟩) r
  apply hi.integral_prod_right.congr
  exact Eventually.of_forall (integral_scheduledPairOperator_inverse_circle_eq
    j T α d₁ d₂ ρ₁ ρ₂ E width K I₁ I₂ r)

theorem preparedInverseCircleKernelSeries_spatial_eq (T : ℕ) (α : ℝ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + 2 * T ≤ K)
    (horder₂ : d₂.order I₂ + 2 * T ≤ K) (r : ℝ) :
    (Real.sqrt r : ℂ) * ∫ z, preparedInverseCircleKernelSeries T α
      (builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
        (d₂.symbol ρ₂ E width K I₂) z.1 z.2) (z.1 - z.2) r
        ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) =
      ∑ j ∈ range T, (r : ℂ)⁻¹ ^ j *
        scheduledPairOperatorPairing (stationaryPhaseInversePolynomial j) j d₁ d₂
          ρ₁ ρ₂ X Y E width K I₁ I₂ (preparedArcCutoff (6 * T) α) r := by
  have hdeg (j : ℕ) (hj : j ∈ range T) :
      d₁.order I₁ + (stationaryPhaseInversePolynomial j).natDegree ≤ K ∧
      d₂.order I₂ + (stationaryPhaseInversePolynomial j).natDegree ≤ K := by
    have := stationaryPhaseInversePolynomial_natDegree_le j
    have := Finset.mem_range.mp hj
    omega
  have hc (j : ℕ) (z : Plane × Plane) :
      ((r * ‖z.1 - z.2‖ : ℝ) : ℂ)⁻¹ ^ j =
        (r : ℂ)⁻¹ ^ j * (((dist z.1 z.2)⁻¹ ^ j : ℝ) : ℂ) := by
    simp only [← dist_eq_norm, Complex.ofReal_mul, mul_inv_rev, mul_pow,
      Complex.ofReal_pow, Complex.ofReal_inv]
    ring
  simp only [preparedInverseCircleKernelSeries, hc, mul_assoc]
  rw [integral_finsetSum _ (fun j hj ↦
    (integrable_spatial_preparedInverseCircleKernel j T α d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY
      hXball hYball E width K I₁ I₂ (hdeg j hj).1 (hdeg j hj).2 r).const_mul _), mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [integral_const_mul, scheduledPairOperatorPairing_inverse_eq j T α d₁ d₂ ρ₁ ρ₂
    hρ hsep hX hY hXball hYball E width K I₁ I₂ (hdeg j hj).1 (hdeg j hj).2 r]
  ring

end FalconerThetaGauge
