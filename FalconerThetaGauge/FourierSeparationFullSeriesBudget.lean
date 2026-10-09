/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationFullSeries

/-! # Actual full-series symbols and uniform coefficient majorants -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

def scheduledPairFullFrequencyMajorant (T : ℕ) (d₁ d₂ : ScheduledSymbolData)
    (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) (x₀ y₀ : Plane) (ρ R : ℝ)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) : ℝ :=
  scheduledPairFrequencyMajorant (stationaryPhaseInversePolynomial z.1.val) z.1.val
    d₁ d₂ E I₁ I₂ x₀ y₀ ρ R z.2

theorem summable_scheduledPairFullFrequencyMajorant (T : ℕ) (d₁ d₂ : ScheduledSymbolData)
    (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {R : ℝ} (hR : 0 < R) :
    Summable (scheduledPairFullFrequencyMajorant T d₁ d₂ E I₁ I₂ x₀ y₀ ρ R) := by
  apply (summable_sigma_of_nonneg (fun _ ↦ mul_nonneg (by positivity) (norm_nonneg _))).mpr
  constructor
  · intro j
    exact summable_scheduledPairFrequencyMajorant _ j.val d₁ d₂ E I₁ I₂ hρ hsep R
  · exact Summable.of_finite (L := SummationFilter.unconditional {j // j ∈ Finset.range T})

theorem norm_scheduledPairFullFrequencyCoefficient_le (T : ℕ) (d₁ d₂ : ScheduledSymbolData)
    (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) (x₀ y₀ : Plane) (ρ : ℝ)
    {R r : ℝ} (hR : 0 < R) (hRr : R ≤ r) (z : ScheduledPairFullInverseBranch T I₁ I₂) :
    ‖scheduledPairFullFrequencyCoefficient T d₁ d₂ E I₁ I₂ x₀ y₀ ρ r z‖ ≤
      scheduledPairFullFrequencyMajorant T d₁ d₂ E I₁ I₂ x₀ y₀ ρ R z :=
  norm_scheduledPairFrequencyCoefficient_le _ z.1.val d₁ d₂ E I₁ I₂ x₀ y₀ ρ hR hRr z.2

theorem scheduledPairFullLeftSymbol_mem_class (T : ℕ) (d : ScheduledSymbolData)
    {x₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) {X : Set Plane}
    (hX : MeasurableSet X) (hXball : X ⊆ closedBall x₀ ρ)
    (ρ₁ : Measure Plane) (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) :
    scheduledPairFullLeftSymbol T d ρ₁ X E width K I₁ I₂ x₀ ρ z ∈
      scheduledSymbolClass ρ₁ E width K I₁ (d.order I₁ + 2 * T) := by
  obtain ⟨d', hd', he⟩ := scheduledPairSeparatedLeftSymbol_mem_class _ d hρ hX hXball
    ρ₁ E width K I₁ I₂ z.2
  refine ⟨d', ?_, he⟩
  have := stationaryPhaseInversePolynomial_natDegree_le z.1.val
  have := Finset.mem_range.mp z.1.property
  omega

theorem scheduledPairFullRightSymbol_mem_class (T : ℕ) (d : ScheduledSymbolData)
    {y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) {Y : Set Plane}
    (hY : MeasurableSet Y) (hYball : Y ⊆ closedBall y₀ ρ)
    (ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) :
    scheduledPairFullRightSymbol T d ρ₂ Y E width K I₁ I₂ y₀ ρ z ∈
      scheduledSymbolClass ρ₂ E width K I₂ (d.order I₂ + 2 * T) := by
  obtain ⟨d', hd', he⟩ := scheduledPairSeparatedRightSymbol_mem_class _ d hρ hY hYball
    ρ₂ E width K I₁ I₂ z.2
  refine ⟨d', ?_, he⟩
  have := stationaryPhaseInversePolynomial_natDegree_le z.1.val
  have := Finset.mem_range.mp z.1.property
  omega

theorem tsum_scheduledPairFullFrequencyMajorant_le (T : ℕ) (d₁ d₂ : ScheduledSymbolData)
    (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    {L₁ L₂ : ℕ} (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (horder₁ : d₁.order I₁ + 2 * T ≤ 8 * T)
    (horder₂ : d₂.order I₂ + 2 * T ≤ 8 * T) {M : ℝ} (hM : 1 ≤ M)
    (hM₁ : scheduledSymbolScale T E I₁ L₁ ≤ M)
    (hM₂ : scheduledSymbolScale T E I₂ L₂ ≤ M)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    (a v : ℝ) (hC : Real.sqrt 2 / dist x₀ y₀ ≤ 6 * (2 : ℝ) ^ a) :
    (∑' z : ScheduledPairFullInverseBranch T I₁ I₂,
      scheduledPairFullFrequencyMajorant T d₁ d₂ E I₁ I₂
        x₀ y₀ ρ ((2 : ℝ) ^ v / 2) z) ≤
      ∑ j ∈ range T, (9600 * T * M ^ 2 * (2 : ℝ) ^ (a - v)) ^ j := by
  have hR : 0 < (2 : ℝ) ^ v / 2 := by positivity
  have ht := summable_scheduledPairFullFrequencyMajorant T d₁ d₂ E I₁ I₂ hρ hsep hR
  unfold ScheduledPairFullInverseBranch at ht ⊢
  rw [ht.tsum_sigma' (fun j ↦
    summable_scheduledPairFrequencyMajorant _ j.val d₁ d₂ E I₁ I₂ hρ hsep _), tsum_fintype]
  rw [← sum_coe_sort (range T) (fun j ↦
    (9600 * T * M ^ 2 * (2 : ℝ) ^ (a - v)) ^ j)]
  apply sum_le_sum
  intro j _
  have hj : j.val ≤ T := by have := Finset.mem_range.mp j.property; omega
  exact tsum_scheduledPairFrequencyMajorant_inverse_dyadic_le hj d₁ d₂ E I₁ I₂
    hL₁ hL₂ (by omega) (by omega) hM hM₁ hM₂ hρ hsep a v hC

end FalconerThetaGauge
