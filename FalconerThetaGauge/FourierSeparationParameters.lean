/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationCoefficientDecay

/-! # Source parameter facts imply the actual full Fourier coefficient budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem tsum_scheduledPairFullFrequencyMajorant_le_of_parameters {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (d₁ d₂ : ScheduledSymbolData)
    (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (horder₁ : d₁.order I₁ + 2 * expansionCount θ N ≤ 8 * expansionCount θ N)
    (horder₂ : d₂.order I₂ + 2 * expansionCount θ N ≤ 8 * expansionCount θ N)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    (a v : ℝ) (hC : Real.sqrt 2 / dist x₀ y₀ ≤ 6 * (2 : ℝ) ^ a)
    (hw : 10 * (tolerance θ N * N) ≤ v - a)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ v - a + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ v - a + tolerance θ N * N) :
    (∑' z : ScheduledPairFullInverseBranch (expansionCount θ N) I₁ I₂,
      scheduledPairFullFrequencyMajorant (expansionCount θ N) d₁ d₂
        (tolerance θ N * N) I₁ I₂ x₀ y₀ ρ ((2 : ℝ) ^ v / 2) z) ≤ 11 / 10 := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let M := scheduledPairCommonScale T E I₁ I₂ L₁ L₂
  have hN : 0 < N := by have := hpar.1; omega
  have hT : 1 ≤ T := Nat.ceil_pos.mpr (by have := tolerance_pos θ hN; positivity)
  have hE : 16 ≤ E := hpar.2.2.1.1
  have hM : 1 ≤ M := one_le_scheduledPairCommonScale T E I₁ I₂ L₁ L₂
  have hM₀ : 0 ≤ M := by linarith
  have hMfreq := scheduledPairCommonScale_le_frequency hT N (by linarith : 0 ≤ E) hw
    I₁ I₂ hc₁ hc₂ hlength₁ hlength₂
  have hbase : 9600 * T * M ^ 2 * (2 : ℝ) ^ (a - v) ≤
      (2 : ℝ) ^ (-(7 * E / 8)) := by
    rw [show a - v = -(v - a) by ring]
    exact mattila_coefficient_base_le hM₀ hMfreq hpar.2.1
  have hfull := tsum_scheduledPairFullFrequencyMajorant_le T d₁ d₂ E I₁ I₂ hL₁ hL₂
    horder₁ horder₂ hM (scheduledSymbolScale_left_le_common T E I₁ I₂ L₁ L₂)
    (scheduledSymbolScale_right_le_common T E I₁ I₂ L₁ L₂) hρ hsep a v hC
  exact hfull.trans ((sum_le_sum (fun j _ ↦
    pow_le_pow_left₀ (by positivity) hbase j)).trans (source_coefficient_decay_sum_le T hE))

theorem scheduledPairFullLeftMaskSymbol_mem_class (T : ℕ)
    {x₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) {X : Set Plane}
    (hX : MeasurableSet X) (hXball : X ⊆ closedBall x₀ ρ)
    (ρ₁ : Measure Plane) (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) :
    scheduledPairFullLeftSymbol T .maskProduct ρ₁ X E width K I₁ I₂ x₀ ρ z ∈
      scheduledSymbolClass ρ₁ E width K I₁ (2 * T) := by
  simpa only [ScheduledSymbolData.maskProduct_order, zero_add] using
    scheduledPairFullLeftSymbol_mem_class T .maskProduct hρ hX hXball ρ₁ E width K I₁ I₂ z

theorem scheduledPairFullRightMaskSymbol_mem_class (T : ℕ)
    {y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) {Y : Set Plane}
    (hY : MeasurableSet Y) (hYball : Y ⊆ closedBall y₀ ρ)
    (ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (z : ScheduledPairFullInverseBranch T I₁ I₂) :
    scheduledPairFullRightSymbol T .maskProduct ρ₂ Y E width K I₁ I₂ y₀ ρ z ∈
      scheduledSymbolClass ρ₂ E width K I₂ (2 * T) := by
  simpa only [ScheduledSymbolData.maskProduct_order, zero_add] using
    scheduledPairFullRightSymbol_mem_class T .maskProduct hρ hY hYball ρ₂ E width K I₁ I₂ z

end FalconerThetaGauge
