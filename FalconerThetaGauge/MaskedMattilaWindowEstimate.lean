/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaWindowIntegrability

/-! # The actual masked distance Fourier estimate on a positive frequency window -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric
open scoped Classical

namespace FalconerThetaGauge

def builtMaskedDistanceMeasure (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (E width : ℝ) (K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) : Measure ℝ :=
  filteredCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y)
    (directionalPairMask (ScheduledSymbolData.maskProduct.symbol ρ₁ E width K I₁)
      (ScheduledSymbolData.maskProduct.symbol ρ₂ E width K I₂))

def maskedMattilaPreparedSpatialSeries (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (E width α : ℝ) (T : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) (r : ℝ) : ℂ :=
  (Real.sqrt r : ℂ) * ∫ z, preparedInverseCircleKernelSeries T α
    (builtSymbolPairAngularAmplitude
      (ScheduledSymbolData.maskProduct.symbol ρ₁ E width (8 * T) I₁)
      (ScheduledSymbolData.maskProduct.symbol ρ₂ E width (8 * T) I₂) z.1 z.2)
      (z.1 - z.2) r ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)

theorem integral_sq_le_of_uniform_error {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {f g : A → ℂ} {c : ℂ} {ε : ℝ}
    (hf : Integrable (fun x ↦ ‖f x‖ ^ 2) μ)
    (hg : Integrable (fun x ↦ ‖g x‖ ^ 2) μ)
    (herr : ∀ᵐ x ∂μ, ‖f x - c * g x‖ ≤ ε) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) ≤
      2 * ‖c‖ ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂μ) + 2 * ε ^ 2 * μ.real univ := by
  have hp : ∀ᵐ x ∂μ, ‖f x‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 * ‖g x‖ ^ 2 + 2 * ε ^ 2 := by
    filter_upwards [herr] with x hx
    have ht : ‖f x‖ ≤ ‖c‖ * ‖g x‖ + ε := by
      calc
        _ = ‖c * g x + (f x - c * g x)‖ := by congr 1; ring
        _ ≤ ‖c * g x‖ + ‖f x - c * g x‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_mul]; linarith
    have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith [sq_nonneg (‖c‖ * ‖g x‖ - ε)]
  calc
    _ ≤ ∫ x, 2 * ‖c‖ ^ 2 * ‖g x‖ ^ 2 + 2 * ε ^ 2 ∂μ :=
      integral_mono_ae hf ((hg.const_mul _).add (integrable_const _)) hp
    _ = _ := by
      rw [integral_add (hg.const_mul _) (integrable_const _), integral_const_mul]
      simp [mul_comm]

theorem norm_preparedCircleInversionConstant_sq :
    ‖preparedCircleInversionConstant‖ ^ 2 = (2 * Real.pi)⁻¹ := by
  rw [norm_preparedCircleInversionConstant, inv_pow, Real.sq_sqrt (by positivity)]

set_option maxHeartbeats 800000 in
theorem integral_builtMaskedDistance_window_le {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (width α a : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) (cutoffK v : ℕ)
    (hC : Real.sqrt 2 / dist x₀ y₀ ≤ 6 * (2 : ℝ) ^ a)
    (hdir : ∀ x ∈ X, ∀ y ∈ Y, pairDirection x y ∈ closedDirectionArc α (1 / 40))
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - a)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hΛ : ∀ r ∈ bilinearFrequencyWindow v, ∀ x ∈ X, ∀ y ∈ Y,
      (2 : ℝ) ^ ((v : ℝ) - a - 4) ≤ r * dist x y)
    (hterminal : ∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ dist x y) :
    (∫ r in bilinearFrequencyWindow v,
      ‖angularScalarFourier (builtMaskedDistanceMeasure ρ₁ ρ₂ X Y
        (tolerance θ N * N) width (8 * expansionCount θ N) I₁ I₂) r‖ ^ 2) ≤
      121 / (50 * Real.pi) * (ρ₁.real X * ρ₂.real Y) *
        scheduledFourierEnergySup ρ₁ ρ₂ X Y (tolerance θ N * N) width
          (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v +
      3 * (2 : ℝ) ^ v * ((2 : ℝ) ^ (-(200 * (N : ℝ)))) ^ 2 *
        (ρ₁.real X * ρ₂.real Y) ^ 2 := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let β := builtMaskedDistanceMeasure ρ₁ ρ₂ X Y E width (8 * T) I₁ I₂
  let S := maskedMattilaPreparedSpatialSeries ρ₁ ρ₂ X Y E width α T I₁ I₂
  let m := ρ₁.real X * ρ₂.real Y
  let ε := (2 : ℝ) ^ (-(200 * (N : ℝ))) * m
  have hbound₁ (x w) : ScheduledSymbolData.maskProduct.symbol
      ρ₁ E width (8 * T) I₁ x w ∈ Icc 0 1 := by
    rw [ScheduledSymbolData.maskProduct_symbol]
    exact scheduledWidthMaskProduct_mem_Icc _ _ _ _ _ _ _
  have hbound₂ (x w) : ScheduledSymbolData.maskProduct.symbol
      ρ₂ E width (8 * T) I₂ x w ∈ Icc 0 1 := by
    rw [ScheduledSymbolData.maskProduct_symbol]
    exact scheduledWidthMaskProduct_mem_Icc _ _ _ _ _ _ _
  let : IsFiniteMeasure β := isFiniteMeasure_maskedDistance ρ₁ ρ₂ hX hY
    (by positivity : 0 < (2 : ℝ) ^ (-(N : ℝ) - 4)) hterminal hbound₁ hbound₂
  let : IsFiniteMeasure (volume.restrict (bilinearFrequencyWindow v)) := by
    unfold bilinearFrequencyWindow
    infer_instance
  have hβ : IntegrableOn (fun r ↦ ‖angularScalarFourier β r‖ ^ 2)
      (bilinearFrequencyWindow v) :=
    ((continuous_angularScalarFourier β).norm.pow 2).integrableOn_Icc
  have hS : IntegrableOn (fun r ↦ ‖S r‖ ^ 2) (bilinearFrequencyWindow v) :=
    integrableOn_preparedInverseCircleKernelSeries_sq T α ρ₁ ρ₂ hρ hsep hX hY
      hXball hYball E width I₁ I₂ v
  have herr : ∀ᵐ r ∂volume.restrict (bilinearFrequencyWindow v),
      ‖angularScalarFourier β r - preparedCircleInversionConstant * S r‖ ≤ ε := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have he := norm_maskedDistance_mattila_inversion_error hpar ρ₁ ρ₂ hρ hsep hX hY
      hXball hYball width α ((v : ℝ) - a) I₁ I₂ hL₁ hL₂ hc₁ hc₂ hL₁N hL₂N
      (bilinearFrequencyWindow_subset_positive v hr) hdir hw hlength₁ hlength₂
      (hΛ r hr) hterminal
    simpa only [β, S, builtMaskedDistanceMeasure, maskedMattilaPreparedSpatialSeries,
      E, T, ε, m, mul_assoc] using he
  have hi := integral_sq_le_of_uniform_error (μ := volume.restrict (bilinearFrequencyWindow v))
    hβ hS herr
  have hStep3 := integral_preparedInverseCircleKernelSeries_sq_le hpar ρ₁ ρ₂ hρ hsep
    hX hY hXball hYball width α a I₁ I₂ hL₁ hL₂ hc₁ hc₂ cutoffK v hC hw
      hlength₁ hlength₂
  have hmass : (volume.restrict (bilinearFrequencyWindow v)).real univ =
      3 / 2 * (2 : ℝ) ^ v := by
    have hp : 0 < (2 : ℝ) ^ v := by positivity
    rw [Measure.real, Measure.restrict_apply_univ, bilinearFrequencyWindow,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [norm_preparedCircleInversionConstant_sq, hmass] at hi
  apply hi.trans
  calc
    _ ≤ 2 * (2 * Real.pi)⁻¹ *
        (121 / 50 * m * scheduledFourierEnergySup ρ₁ ρ₂ X Y E width
          (8 * T) I₁ I₂ (2 * T) cutoffK v) +
        2 * ε ^ 2 * (3 / 2 * (2 : ℝ) ^ v) := by
      gcongr
      exact hStep3
    _ = _ := by
      dsimp [ε, m, T, E]
      field_simp

end FalconerThetaGauge
