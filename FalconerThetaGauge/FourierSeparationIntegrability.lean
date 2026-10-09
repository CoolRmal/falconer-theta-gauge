/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationIntegral

/-! # Integrability of the actual separated inverse-power kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

theorem integrable_inversePowerCircleKernel (j : ℕ)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    Integrable (inversePowerCircleKernel j b₁ b₂ ψ r)
      (circleArcLength.prod ((ρ₁.restrict X).prod (ρ₂.restrict Y))) := by
  have hs := summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep
  apply (integrable_const
    (∑' n, |spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n|)).mono
    (measurable_inversePowerCircleKernel j hb₁ hb₂ hψ r).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually
    (ae_restricted_product_carriers ρ₁ ρ₂ hX hY)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun n ↦ abs_nonneg _))]
  have hpSum := hasSum_separatedInversePowerKernelTerm
    j hρ hsep hXball hYball b₁ b₂ ψ r p hp
  exact hpSum.norm_le_of_bounded hs.hasSum
    (fun n ↦ norm_separatedInversePowerKernelTerm_le j hρ hXball hYball
      hbound₁ hbound₂ hψ₁ r n p)

theorem integral_inversePowerCircleKernel_eq (j : ℕ)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    (∫ p, inversePowerCircleKernel j b₁ b₂ ψ r p
      ∂circleArcLength.prod ((ρ₁.restrict X).prod (ρ₂.restrict Y))) =
      ∫ p, ((dist p.1 p.2)⁻¹ ^ j : ℝ) *
        (∫ w, (ψ w : ℂ) * maskedFourierPairKernel b₁ b₂ r w p ∂circleArcLength)
          ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) := by
  rw [integral_prod_symm _ (integrable_inversePowerCircleKernel j ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁ r)]
  apply integral_congr_ae
  filter_upwards [] with p
  change (∫ w, (((dist p.1 p.2)⁻¹ ^ j : ℝ) : ℂ) *
    ((ψ w : ℂ) * maskedFourierPairKernel b₁ b₂ r w p) ∂circleArcLength) = _
  exact integral_const_mul _ _

end FalconerThetaGauge
