/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaShellEstimate

/-! # The source's normalized Estimate 7.5 for actual level masks -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

theorem builtMaskedDistanceMeasure_eq_level (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (E : ℝ) (L i K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) :
    builtMaskedDistanceMeasure ρ₁ ρ₂ X Y E (directionalLevelWidth L i) K I₁ I₂ =
      levelMaskedDistanceMeasure ρ₁ ρ₂ X Y E L i K I₁ I₂ := by
  simp only [builtMaskedDistanceMeasure, levelMaskedDistanceMeasure,
    ScheduledSymbolData.maskProduct_symbol]

set_option maxHeartbeats 800000 in
theorem builtMaskedDistance_mattila_shell_normalized_estimate {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hm : 0 < ρ₁.real X * ρ₂.real Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (width α a : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) (cutoffK v : ℕ) (hv : v ≤ N)
    (hC : Real.sqrt 2 / dist x₀ y₀ ≤ 6 * (2 : ℝ) ^ a)
    (hdir : ∀ x ∈ X, ∀ y ∈ Y, pairDirection x y ∈ closedDirectionArc α (1 / 40))
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - a)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hΛ : ∀ r ∈ bilinearFrequencyWindow v, ∀ x ∈ X, ∀ y ∈ Y,
      (2 : ℝ) ^ ((v : ℝ) - a - 4) ≤ r * dist x y)
    (hterminal : ∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ dist x y) :
    scalarDyadicFourierShellIntegral
        (builtMaskedDistanceMeasure ρ₁ ρ₂ X Y (tolerance θ N * N) width
          (8 * expansionCount θ N) I₁ I₂) v / (ρ₁.real X * ρ₂.real Y) ≤
      2 * scheduledFourierEnergySup ρ₁ ρ₂ X Y (tolerance θ N * N) width
        (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v +
      (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  have hs := builtMaskedDistance_mattila_shell_estimate hpar ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball width α a I₁ I₂ hL₁ hL₂ hc₁ hc₂ hL₁N hL₂N cutoffK v hv hC
    hdir hw hlength₁ hlength₂ hΛ hterminal
  have hm₁ : ρ₁.real X * ρ₂.real Y ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul measureReal_le_one measureReal_le_one
        (by positivity) (by norm_num)
      _ = _ := one_mul _
  apply (div_le_iff₀ hm).mpr
  calc
    _ ≤ 2 * (ρ₁.real X * ρ₂.real Y) *
        scheduledFourierEnergySup ρ₁ ρ₂ X Y (tolerance θ N * N) width
          (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v +
        (2 : ℝ) ^ (-(390 * (N : ℝ))) * (ρ₁.real X * ρ₂.real Y) ^ 2 := hs
    _ ≤ 2 * (ρ₁.real X * ρ₂.real Y) *
        scheduledFourierEnergySup ρ₁ ρ₂ X Y (tolerance θ N * N) width
          (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v +
        (2 : ℝ) ^ (-(390 * (N : ℝ))) * (ρ₁.real X * ρ₂.real Y) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = _ := by ring

end FalconerThetaGauge
