/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationParameters
public import FalconerThetaGauge.FourierBilinearSeriesExpansion
public import FalconerThetaGauge.ScheduledSymbolEnergy

/-! # The genuine integrated Step 3 bound for the full prepared inverse series -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric Polynomial Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem integral_preparedInverseCircleKernelSeries_sq_le {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (width α a : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1) (cutoffK v : ℕ)
    (hC : Real.sqrt 2 / dist x₀ y₀ ≤ 6 * (2 : ℝ) ^ a)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - a)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N) :
    (∫ r in bilinearFrequencyWindow v,
      ‖(Real.sqrt r : ℂ) * ∫ z, preparedInverseCircleKernelSeries (expansionCount θ N) α
        (builtSymbolPairAngularAmplitude
          (ScheduledSymbolData.maskProduct.symbol ρ₁ (tolerance θ N * N) width
            (8 * expansionCount θ N) I₁)
          (ScheduledSymbolData.maskProduct.symbol ρ₂ (tolerance θ N * N) width
            (8 * expansionCount θ N) I₂) z.1 z.2) (z.1 - z.2) r
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)‖ ^ 2) ≤
      121 / 50 * (ρ₁.real X * ρ₂.real Y) *
        scheduledFourierEnergySup ρ₁ ρ₂ X Y (tolerance θ N * N) width
          (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let R := (2 : ℝ) ^ v / 2
  let b₁ := scheduledPairFullLeftSymbol T .maskProduct ρ₁ X E width (8 * T) I₁ I₂ x₀ ρ
  let b₂ := scheduledPairFullRightSymbol T .maskProduct ρ₂ Y E width (8 * T) I₁ I₂ y₀ ρ
  let c := fun z r ↦ scheduledPairFullFrequencyCoefficient T .maskProduct .maskProduct
    E I₁ I₂ x₀ y₀ ρ r z
  let A := scheduledPairFullFrequencyMajorant T .maskProduct .maskProduct E I₁ I₂ x₀ y₀ ρ R
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
  have hR : 0 < R := by positivity
  have hA (z) : 0 ≤ A z := mul_nonneg (by positivity) (norm_nonneg _)
  have hsA : Summable A :=
    summable_scheduledPairFullFrequencyMajorant T .maskProduct .maskProduct E I₁ I₂ hρ hsep hR
  have hbudget : ∑' z, A z ≤ 11 / 10 := by
    simpa only [Real.rpow_natCast] using
      tsum_scheduledPairFullFrequencyMajorant_le_of_parameters hpar .maskProduct .maskProduct
        I₁ I₂ hL₁ hL₂ hc₁ hc₂
        (by simp only [ScheduledSymbolData.maskProduct_order]; omega)
        (by simp only [ScheduledSymbolData.maskProduct_order]; omega)
        hρ hsep a (v : ℝ) hC hw hlength₁ hlength₂
  have hψ₁ (w) : |preparedArcCutoff (6 * T) α w| ≤ 1 := abs_le.mpr
    ⟨by linarith [(preparedArcCutoff_mem_Icc (6 * T) α w).1],
      (preparedArcCutoff_mem_Icc (6 * T) α w).2⟩
  have hineq := integral_tsum_maskedFourierBilinearAmplitude_sq_le ρ₁ ρ₂ X Y
    hb₁ hb₂ hbound₁ hbound₂ (measurable_preparedArcCutoff _ _) hψ₁ cutoffK v
    (fun z ↦ measurable_scheduledPairFullFrequencyCoefficient T .maskProduct .maskProduct
      E I₁ I₂ x₀ y₀ ρ z) hA hsA
    (fun z r hr ↦ norm_scheduledPairFullFrequencyCoefficient_le
      T .maskProduct .maskProduct E I₁ I₂ x₀ y₀ ρ hR hr.1 z)
  have he (r : ℝ) : (∑' z, c z r *
      maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y (b₁ z) (b₂ z)
        (preparedArcCutoff (6 * T) α) r) =
      (Real.sqrt r : ℂ) * ∫ z, preparedInverseCircleKernelSeries T α
        (builtSymbolPairAngularAmplitude
          (ScheduledSymbolData.maskProduct.symbol ρ₁ E width (8 * T) I₁)
          (ScheduledSymbolData.maskProduct.symbol ρ₂ E width (8 * T) I₂) z.1 z.2)
          (z.1 - z.2) r
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) :=
    (preparedInverseCircleKernelSeries_spatial_hasSum T α .maskProduct .maskProduct ρ₁ ρ₂
      hρ hsep hX hY hXball hYball E width (8 * T) I₁ I₂
      (by simp only [ScheduledSymbolData.maskProduct_order]; omega)
      (by simp only [ScheduledSymbolData.maskProduct_order]; omega) r).tsum_eq
  rw [show (fun r ↦ ‖∑' z, c z r * maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y
      (b₁ z) (b₂ z) (preparedArcCutoff (6 * T) α) r‖ ^ 2) = _ from
      funext (fun r ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) (he r))] at hineq
  let F := scheduledFourierEnergySup ρ₁ ρ₂ X Y E width (8 * T) I₁ I₂ (2 * T) cutoffK v
  have hF : 0 ≤ F := scheduledFourierEnergySup_nonneg ρ₁ ρ₂ X Y E width
    (8 * T) I₁ I₂ (by omega) cutoffK v
  have hsAF := summable_weighted_maskedFourierEnergy hA hsA ρ₁ ρ₂ X Y
    hb₁ hb₂ hbound₁ hbound₂ cutoffK v
  have hAF : (∑' z, A z * maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ z) (b₂ z) cutoffK v) ≤
      (∑' z, A z) * F := by
    calc
      _ ≤ ∑' z, A z * F := Summable.tsum_le_tsum
        (fun z ↦ mul_le_mul_of_nonneg_left
          (maskedFourierEnergy_le_scheduledFourierEnergySup ρ₁ ρ₂ X Y E width
            (8 * T) I₁ I₂ (by omega) cutoffK v (hclass₁ z) (hclass₂ z)) (hA z))
        hsAF (hsA.mul_right F)
      _ = _ := tsum_mul_right
  apply hineq.trans
  calc
    _ ≤ 2 * (ρ₁.real X * ρ₂.real Y) * (11 / 10) * ((11 / 10) * F) := by
      gcongr
      · exact tsum_nonneg (fun z ↦ mul_nonneg (hA z)
          (maskedFourierEnergy_nonneg ρ₁ ρ₂ X Y (b₁ z) (b₂ z) cutoffK v))
      · exact hAF.trans (mul_le_mul_of_nonneg_right hbudget hF)
    _ = _ := by ring

end FalconerThetaGauge
