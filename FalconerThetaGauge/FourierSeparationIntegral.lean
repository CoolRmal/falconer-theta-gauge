/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationSeries

/-! # The actual separated polynomial Fourier series obtained by Fubini -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

theorem separated_inversePower_circleIntegral_hasSum (j : ℕ)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    HasSum (fun n ↦ (spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n : ℂ) *
      ∫ w, (ψ w : ℂ) *
        maskedFourierAmplitude ρ₁ X
          (carrierPolynomialSymbol X (spatialInversePowerSequenceLeftPolynomial x₀ ρ n) b₁)
          r w * star (maskedFourierAmplitude ρ₂ Y
          (carrierPolynomialSymbol Y (spatialInversePowerSequenceRightPolynomial y₀ ρ n) b₂)
          r w) ∂circleArcLength)
      (∫ p, ((dist p.1 p.2)⁻¹ ^ j : ℝ) *
        (∫ w, (ψ w : ℂ) * maskedFourierPairKernel b₁ b₂ r w p ∂circleArcLength)
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  let μ := (ρ₁.restrict X).prod (ρ₂.restrict Y)
  let F := separatedInversePowerKernelTerm j x₀ y₀ ρ X Y b₁ b₂ ψ r
  let G := inversePowerCircleKernel j b₁ b₂ ψ r
  let c := spatialInversePowerSequenceCoefficient j x₀ y₀ ρ
  have hs := summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep
  have hFm : ∀ n, Measurable (F n) := fun n ↦
    (measurable_const.mul (hψ.comp measurable_fst).complex_ofReal).mul
      (measurable_maskedFourierPairKernel
        (measurable_carrierPolynomialSymbol hX _ hb₁)
        (measurable_carrierPolynomialSymbol hY _ hb₂) r)
  have hFn : ∀ n p, ‖F n p‖ ≤ |c n| :=
    norm_separatedInversePowerKernelTerm_le j hρ hXball hYball hbound₁ hbound₂ hψ₁ r
  have hFi : ∀ n, Integrable (F n) (circleArcLength.prod μ) := by
    intro n
    exact (integrable_const |c n|).mono (hFm n).aestronglyMeasurable
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs, abs_abs] using hFn n p))
  have hpoint : ∀ᵐ p ∂circleArcLength.prod μ, HasSum (fun n ↦ F n p) (G p) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually
      (ae_restricted_product_carriers ρ₁ ρ₂ hX hY)] with p hp
    exact hasSum_separatedInversePowerKernelTerm j hρ hsep hXball hYball b₁ b₂ ψ r p hp
  have hGi : Integrable G (circleArcLength.prod μ) := by
    apply (integrable_const (∑' n, |c n|)).mono
      (measurable_inversePowerCircleKernel j hb₁ hb₂ hψ r).aestronglyMeasurable
    filter_upwards [hpoint] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun n ↦ abs_nonneg (c n)))]
    exact hp.norm_le_of_bounded hs.hasSum (fun n ↦ hFn n p)
  have hleft (n : ℕ) : (∫ p, F n p ∂circleArcLength.prod μ) = (c n : ℂ) *
      ∫ w, (ψ w : ℂ) *
        maskedFourierAmplitude ρ₁ X
          (carrierPolynomialSymbol X (spatialInversePowerSequenceLeftPolynomial x₀ ρ n) b₁)
          r w * star (maskedFourierAmplitude ρ₂ Y
          (carrierPolynomialSymbol Y (spatialInversePowerSequenceRightPolynomial y₀ ρ n) b₂)
          r w) ∂circleArcLength := by
    rw [integral_prod _ (hFi n)]
    simp only [F, separatedInversePowerKernelTerm, mul_assoc, μ, c]
    simp_rw [integral_const_mul, integral_maskedFourierPairKernel]
  have hright : (∫ p, G p ∂circleArcLength.prod μ) =
      (∫ p, ((dist p.1 p.2)⁻¹ ^ j : ℝ) *
        (∫ w, (ψ w : ℂ) * maskedFourierPairKernel b₁ b₂ r w p ∂circleArcLength)
          ∂μ) := by
    rw [integral_prod_symm _ hGi]
    apply integral_congr_ae
    filter_upwards [] with p
    change (∫ w, (((dist p.1 p.2)⁻¹ ^ j : ℝ) : ℂ) *
      ((ψ w : ℂ) * maskedFourierPairKernel b₁ b₂ r w p) ∂circleArcLength) = _
    exact integral_const_mul _ _
  have h := hasSum_integral_separatedInversePowerKernelTerm j ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁ r
  change HasSum (fun n ↦ ∫ p, F n p ∂circleArcLength.prod μ)
    (∫ p, G p ∂circleArcLength.prod μ) at h
  simpa only [hleft, hright] using h

end FalconerThetaGauge
