/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationFullInversion

/-! # The genuine countable Fourier series of the full prepared inverse -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem hasSum_finite_complex_sigma {ι : Type*} [Fintype ι] (β : ι → Type*)
    (f : (i : ι) → β i → ℂ) (g : ι → ℂ) (hf : ∀ i, HasSum (f i) (g i)) :
    HasSum (fun z : Sigma β ↦ f z.1 z.2) (∑ i, g i) := by
  have hn : Summable (fun z : Sigma β ↦ ‖f z.1 z.2‖) := by
    apply (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
    constructor
    · intro i
      exact (hf i).summable.norm
    · exact Summable.of_finite (L := SummationFilter.unconditional ι)
  exact HasSum.sigma_of_hasSum (hasSum_fintype g) hf hn.of_norm

def ScheduledPairFullInverseBranch (T : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) :=
  Σ j : {j // j ∈ range T},
    ScheduledPairOperatorBranch (stationaryPhaseInversePolynomial j.val) I₁ I₂ × ℕ

instance (T : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) :
    Countable (ScheduledPairFullInverseBranch T I₁ I₂) := by
  unfold ScheduledPairFullInverseBranch
  infer_instance

def scheduledPairFullFrequencyCoefficient (T : ℕ) (d₁ d₂ : ScheduledSymbolData)
    (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) (x₀ y₀ : Plane) (ρ r : ℝ)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) : ℂ :=
  scheduledPairFrequencyCoefficient (stationaryPhaseInversePolynomial z.1.val) z.1.val
    d₁ d₂ E I₁ I₂ x₀ y₀ ρ r z.2

@[fun_prop]
theorem measurable_scheduledPairFullFrequencyCoefficient (T : ℕ)
    (d₁ d₂ : ScheduledSymbolData) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (x₀ y₀ : Plane) (ρ : ℝ) (z : ScheduledPairFullInverseBranch T I₁ I₂) :
    Measurable (fun r ↦
      scheduledPairFullFrequencyCoefficient T d₁ d₂ E I₁ I₂ x₀ y₀ ρ r z) :=
  measurable_scheduledPairFrequencyCoefficient _ z.1.val d₁ d₂ E I₁ I₂ x₀ y₀ ρ z.2

def scheduledPairFullLeftSymbol (T : ℕ) (d : ScheduledSymbolData)
    (ρ₁ : Measure Plane) (X : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (x₀ : Plane) (ρ : ℝ)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) : Plane → UnitCircle → ℝ :=
  scheduledPairSeparatedLeftSymbol (stationaryPhaseInversePolynomial z.1.val)
    d ρ₁ X E width K I₁ I₂ x₀ ρ z.2

def scheduledPairFullRightSymbol (T : ℕ) (d : ScheduledSymbolData)
    (ρ₂ : Measure Plane) (Y : Set Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (y₀ : Plane) (ρ : ℝ)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) : Plane → UnitCircle → ℝ :=
  scheduledPairSeparatedRightSymbol (stationaryPhaseInversePolynomial z.1.val)
    d ρ₂ Y E width K I₁ I₂ y₀ ρ z.2

theorem preparedInverseCircleKernelSeries_spatial_hasSum (T : ℕ) (α : ℝ)
    (d₁ d₂ : ScheduledSymbolData)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (horder₁ : d₁.order I₁ + 2 * T ≤ K)
    (horder₂ : d₂.order I₂ + 2 * T ≤ K) (r : ℝ) :
    HasSum (fun z : ScheduledPairFullInverseBranch T I₁ I₂ ↦
      scheduledPairFullFrequencyCoefficient T d₁ d₂ E I₁ I₂ x₀ y₀ ρ r z *
        maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y
          (scheduledPairFullLeftSymbol T d₁ ρ₁ X E width K I₁ I₂ x₀ ρ z)
          (scheduledPairFullRightSymbol T d₂ ρ₂ Y E width K I₁ I₂ y₀ ρ z)
          (preparedArcCutoff (6 * T) α) r)
      ((Real.sqrt r : ℂ) * ∫ z, preparedInverseCircleKernelSeries T α
        (builtSymbolPairAngularAmplitude (d₁.symbol ρ₁ E width K I₁)
          (d₂.symbol ρ₂ E width K I₂) z.1 z.2) (z.1 - z.2) r
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  have hf (j : {j // j ∈ range T}) :=
    (scheduledPairOperatorPairing_hasSum (stationaryPhaseInversePolynomial j.val) j.val
      d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY
      hXball hYball E width K I₁ I₂
      (by have := Finset.mem_range.mp j.property
          have := stationaryPhaseInversePolynomial_natDegree_le j.val; omega)
      (by have := Finset.mem_range.mp j.property
          have := stationaryPhaseInversePolynomial_natDegree_le j.val; omega)
      (measurable_preparedArcCutoff _ _) (fun w ↦ abs_le.mpr
        ⟨by linarith [(preparedArcCutoff_mem_Icc (6 * T) α w).1],
          (preparedArcCutoff_mem_Icc (6 * T) α w).2⟩) r).mul_left
      ((r : ℂ)⁻¹ ^ j.val)
  rw [preparedInverseCircleKernelSeries_spatial_eq T α d₁ d₂ ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball E width K I₁ I₂ horder₁ horder₂ r, ← sum_coe_sort]
  simpa only [ScheduledPairFullInverseBranch, scheduledPairFullFrequencyCoefficient,
    scheduledPairFrequencyCoefficient, scheduledPairFullLeftSymbol, scheduledPairFullRightSymbol,
    mul_assoc] using hasSum_finite_complex_sigma _ _ _ hf

end FalconerThetaGauge
