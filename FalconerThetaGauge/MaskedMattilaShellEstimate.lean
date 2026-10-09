/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaShellReduction

/-! # The actual Mattila shell estimate in source Estimate 7.5 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

theorem isFiniteMeasure_builtMaskedDistanceMeasure
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    {d : ℝ} (hd : 0 < d) (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) :
    IsFiniteMeasure (builtMaskedDistanceMeasure ρ₁ ρ₂ X Y E width K I₁ I₂) := by
  apply isFiniteMeasure_maskedDistance ρ₁ ρ₂ hX hY hd hsep
  · intro x w
    rw [ScheduledSymbolData.maskProduct_symbol]
    exact scheduledWidthMaskProduct_mem_Icc _ _ _ _ _ _ _
  · intro x w
    rw [ScheduledSymbolData.maskProduct_symbol]
    exact scheduledWidthMaskProduct_mem_Icc _ _ _ _ _ _ _

set_option maxHeartbeats 800000 in
theorem builtMaskedDistance_mattila_shell_estimate {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
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
          (8 * expansionCount θ N) I₁ I₂) v ≤
      2 * (ρ₁.real X * ρ₂.real Y) *
        scheduledFourierEnergySup ρ₁ ρ₂ X Y (tolerance θ N * N) width
          (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v +
      (2 : ℝ) ^ (-(390 * (N : ℝ))) * (ρ₁.real X * ρ₂.real Y) ^ 2 := by
  let E := tolerance θ N * N
  let T := expansionCount θ N
  let β := builtMaskedDistanceMeasure ρ₁ ρ₂ X Y E width (8 * T) I₁ I₂
  let m := ρ₁.real X * ρ₂.real Y
  let F := scheduledFourierEnergySup ρ₁ ρ₂ X Y E width (8 * T) I₁ I₂ (2 * T) cutoffK v
  let : IsFiniteMeasure β := isFiniteMeasure_builtMaskedDistanceMeasure ρ₁ ρ₂ hX hY
    (by positivity : 0 < (2 : ℝ) ^ (-(N : ℝ) - 4)) hterminal E width (8 * T) I₁ I₂
  have hF : 0 ≤ F := scheduledFourierEnergySup_nonneg ρ₁ ρ₂ X Y E width
    (8 * T) I₁ I₂ (by omega) cutoffK v
  have hπ : 121 / (25 * Real.pi) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hi := integral_builtMaskedDistance_window_le hpar ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball width α a I₁ I₂ hL₁ hL₂ hc₁ hc₂ hL₁N hL₂N cutoffK v hC
    hdir hw hlength₁ hlength₂ hΛ hterminal
  calc
    _ ≤ 2 * ∫ r in bilinearFrequencyWindow v, ‖angularScalarFourier β r‖ ^ 2 :=
      scalarDyadicFourierShellIntegral_le_twice_window β v
    _ ≤ 2 * (121 / (50 * Real.pi) * m * F +
        3 * (2 : ℝ) ^ v * ((2 : ℝ) ^ (-(200 * (N : ℝ)))) ^ 2 * m ^ 2) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = 121 / (25 * Real.pi) * m * F +
        (6 * (2 : ℝ) ^ v * ((2 : ℝ) ^ (-(200 * (N : ℝ)))) ^ 2) * m ^ 2 := by
      ring
    _ ≤ 2 * m * F + (2 : ℝ) ^ (-(390 * (N : ℝ))) * m ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hπ (by positivity)) hF
      · exact mul_le_mul_of_nonneg_right
          (mattila_shell_error_budget (by have := hpar.1; omega) hv)
          (sq_nonneg _)

end FalconerThetaGauge
