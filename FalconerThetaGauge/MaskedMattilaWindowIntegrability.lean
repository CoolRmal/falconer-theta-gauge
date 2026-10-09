/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaIntegratedInversion

/-! # Integrability of the actual countable inverse series on frequency windows -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric
open scoped Classical

namespace FalconerThetaGauge

theorem integrable_norm_tsum_mul_sq {ι A : Type*} [Countable ι]
    [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    {c z : ι → A → ℂ} {a : ι → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ i, Measurable (c i)) (hz : ∀ i, Measurable (z i))
    (ha : ∀ i, 0 ≤ a i) (has : Summable a)
    (hca : ∀ i, ∀ᵐ x ∂μ, ‖c i x‖ ≤ a i)
    (hzB : ∀ i, ∀ᵐ x ∂μ, ‖z i x‖ ^ 2 ≤ B) :
    Integrable (fun x ↦ ‖∑' i, c i x * z i x‖ ^ 2) μ := by
  have hsum : ∀ᵐ x ∂μ, Summable (fun i ↦ a i * ‖z i x‖ ^ 2) := by
    filter_upwards [ae_all_iff.mpr hzB] with x hx
    exact (has.mul_right B).of_nonneg_of_le
      (fun i ↦ mul_nonneg (ha i) (sq_nonneg _))
      (fun i ↦ mul_le_mul_of_nonneg_left (hx i) (ha i))
  have hbound : ∀ᵐ x ∂μ, ‖∑' i, c i x * z i x‖ ^ 2 ≤ (∑' i, a i) ^ 2 * B := by
    filter_upwards [ae_all_iff.mpr hca, ae_all_iff.mpr hzB, hsum] with x hx hz hs
    calc
      _ ≤ (∑' i, a i) * ∑' i, a i * ‖z i x‖ ^ 2 :=
        norm_tsum_mul_sq_le_weighted ha hx has hs
      _ ≤ (∑' i, a i) * ∑' i, a i * B :=
        mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum
          (fun i ↦ mul_le_mul_of_nonneg_left (hz i) (ha i)) hs (has.mul_right B))
          (tsum_nonneg ha)
      _ = _ := by rw [tsum_mul_right]; ring
  apply (integrable_const ((∑' i, a i) ^ 2 * B)).mono
  · exact ((Measurable.tsum (fun i ↦ (hc i).mul (hz i))).norm.pow_const
      2).aestronglyMeasurable
  · filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hB)]
    exact hx

theorem integrableOn_preparedInverseCircleKernelSeries_sq (T : ℕ) (α : ℝ)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (E width : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) (v : ℕ) :
    IntegrableOn (fun r ↦
      ‖(Real.sqrt r : ℂ) * ∫ z, preparedInverseCircleKernelSeries T α
        (builtSymbolPairAngularAmplitude
          (ScheduledSymbolData.maskProduct.symbol ρ₁ E width (8 * T) I₁)
          (ScheduledSymbolData.maskProduct.symbol ρ₂ E width (8 * T) I₂) z.1 z.2)
          (z.1 - z.2) r ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)‖ ^ 2)
      (bilinearFrequencyWindow v) := by
  let b₁ := scheduledPairFullLeftSymbol T .maskProduct ρ₁ X E width (8 * T) I₁ I₂ x₀ ρ
  let b₂ := scheduledPairFullRightSymbol T .maskProduct ρ₂ Y E width (8 * T) I₁ I₂ y₀ ρ
  let c := fun z r ↦ scheduledPairFullFrequencyCoefficient T .maskProduct .maskProduct
    E I₁ I₂ x₀ y₀ ρ r z
  let A := scheduledPairFullFrequencyMajorant T .maskProduct .maskProduct
    E I₁ I₂ x₀ y₀ ρ ((2 : ℝ) ^ v / 2)
  have hclass₁ (z) := scheduledPairFullLeftMaskSymbol_mem_class
    T hρ hX hXball ρ₁ E width (8 * T) I₁ I₂ z
  have hclass₂ (z) := scheduledPairFullRightMaskSymbol_mem_class
    T hρ hY hYball ρ₂ E width (8 * T) I₁ I₂ z
  have hb₁ (z) : Measurable (uncurry (b₁ z)) :=
    measurable_of_mem_scheduledSymbolClass ρ₁ E width (8 * T) I₁ (2 * T) (hclass₁ z)
  have hb₂ (z) : Measurable (uncurry (b₂ z)) :=
    measurable_of_mem_scheduledSymbolClass ρ₂ E width (8 * T) I₂ (2 * T) (hclass₂ z)
  have hbound₁ (z x w) : |b₁ z x w| ≤ 1 :=
    abs_le_one_of_mem_scheduledSymbolClass ρ₁ E width (8 * T) I₁ (by omega) (hclass₁ z) x w
  have hbound₂ (z x w) : |b₂ z x w| ≤ 1 :=
    abs_le_one_of_mem_scheduledSymbolClass ρ₂ E width (8 * T) I₂ (by omega) (hclass₂ z) x w
  have hψ (w) : |preparedArcCutoff (6 * T) α w| ≤ 1 := abs_le.mpr
    ⟨by linarith [(preparedArcCutoff_mem_Icc (6 * T) α w).1],
      (preparedArcCutoff_mem_Icc (6 * T) α w).2⟩
  let : IsFiniteMeasure (volume.restrict (bilinearFrequencyWindow v)) := by
    unfold bilinearFrequencyWindow
    infer_instance
  have hi := integrable_norm_tsum_mul_sq
    (μ := volume.restrict (bilinearFrequencyWindow v))
    (by positivity : 0 ≤ (2 * Real.pi) ^ 2 * (2 * (2 : ℝ) ^ v) *
      (ρ₁.real X * ρ₂.real Y) ^ 2)
    (fun z ↦ measurable_scheduledPairFullFrequencyCoefficient T .maskProduct .maskProduct
      E I₁ I₂ x₀ y₀ ρ z)
    (fun z ↦ measurable_maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y (hb₁ z) (hb₂ z)
      (measurable_preparedArcCutoff _ _))
    (fun z ↦ mul_nonneg (by positivity) (norm_nonneg _))
    (summable_scheduledPairFullFrequencyMajorant T .maskProduct .maskProduct E I₁ I₂
      hρ hsep (by positivity : 0 < (2 : ℝ) ^ v / 2))
    (fun z ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact norm_scheduledPairFullFrequencyCoefficient_le T .maskProduct .maskProduct
        E I₁ I₂ x₀ y₀ ρ (by positivity) hr.1 z)
    (fun z ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact norm_maskedFourierBilinearAmplitude_sq_le_on_window ρ₁ ρ₂ X Y
        (hb₁ z) (hb₂ z) (hbound₁ z) (hbound₂ z) (measurable_preparedArcCutoff _ _)
        hψ v hr)
  have he (r : ℝ) : (∑' z, c z r * maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y
      (b₁ z) (b₂ z) (preparedArcCutoff (6 * T) α) r) =
      (Real.sqrt r : ℂ) * ∫ z, preparedInverseCircleKernelSeries T α
        (builtSymbolPairAngularAmplitude
          (ScheduledSymbolData.maskProduct.symbol ρ₁ E width (8 * T) I₁)
          (ScheduledSymbolData.maskProduct.symbol ρ₂ E width (8 * T) I₂) z.1 z.2)
          (z.1 - z.2) r ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) :=
    (preparedInverseCircleKernelSeries_spatial_hasSum T α .maskProduct .maskProduct ρ₁ ρ₂
      hρ hsep hX hY hXball hYball E width (8 * T) I₁ I₂
      (by simp only [ScheduledSymbolData.maskProduct_order]; omega)
      (by simp only [ScheduledSymbolData.maskProduct_order]; omega) r).tsum_eq
  exact hi.congr (Eventually.of_forall
    (fun r ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) (he r)))

end FalconerThetaGauge
