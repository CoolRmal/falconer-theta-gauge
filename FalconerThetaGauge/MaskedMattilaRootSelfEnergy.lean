/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.ScheduledSymbolEnergyCauchySchwarz

/-! # Source 9.3 Steps 1--2 for the actual retained pieces and their self energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem measurableSet_mattila_unitSquare : MeasurableSet unitSquare := by
  simp only [unitSquare, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_Ico.preimage (by fun_prop)

set_option maxHeartbeats 800000 in
theorem preparedRegularParts_mattila_annulus_le_self_energies
    (μ₁ μ₂ : Measure Plane) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hball₁ : HasGaugeBallBound μ₁ θ C) (hball₂ : HasGaugeBallBound μ₂ θ C)
    {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    {t₁ t₂ : List ℕ}
    (ht₁ : t₁ ∈ regularDyadicKeptTypes μ₁ (tolerance θ N) (blockParameter θ N) N)
    (ht₂ : t₂ ∈ regularDyadicKeptTypes μ₂ (tolerance θ N) (blockParameter θ N) N)
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S₁ S₂ : Set Plane} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hμ₁ : μ₁ S₁ = 1) (hμ₂ : μ₂ S₂ = 1)
    (hS₁ball : S₁ ⊆ ball x₀ (1 / 400)) (hS₂ball : S₂ ⊆ ball y₀ (1 / 400))
    (width : ℝ) (cutoffK : ℕ) :
    let ρ₁ := regularDyadicPartMeasure μ₁ (tolerance θ N) N t₁
    let ρ₂ := regularDyadicPartMeasure μ₂ (tolerance θ N) N t₂
    let E := tolerance θ N * N
    let T := expansionCount θ N
    let I₁ := regularMeasurePieceTests ρ₁ θ N
    let I₂ := regularMeasurePieceTests ρ₂ θ N
    scalarFourierAnnulusIntegral
        (filteredCrossDistanceMeasure ρ₁ ρ₂ (directionalPairMask
          (ScheduledSymbolData.maskProduct.symbol ρ₁ E width (8 * T) I₁)
          (ScheduledSymbolData.maskProduct.symbol ρ₂ E width (8 * T) I₂)))
        ((N : ℝ) - 1) ((N : ℝ) + 1) ≤
      2 * Real.sqrt (scheduledFourierEnergySup ρ₁ ρ₁ unitSquare unitSquare E width
        (8 * T) I₁ I₁ (2 * T) cutoffK N) *
        Real.sqrt (scheduledFourierEnergySup ρ₂ ρ₂ unitSquare unitSquare E width
          (8 * T) I₂ I₂ (2 * T) cutoffK N) + (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  let ρ₁ := regularDyadicPartMeasure μ₁ (tolerance θ N) N t₁
  let ρ₂ := regularDyadicPartMeasure μ₂ (tolerance θ N) N t₂
  let E := tolerance θ N * N
  let T := expansionCount θ N
  let I₁ := regularMeasurePieceTests ρ₁ θ N
  let I₂ := regularMeasurePieceTests ρ₂ θ N
  have hp₁ := regularDyadicPartMeasure_probability μ₁
    (tolerance θ N) (blockParameter θ N) N ht₁
  have hp₂ := regularDyadicPartMeasure_probability μ₂
    (tolerance θ N) (blockParameter θ N) N ht₂
  let : IsProbabilityMeasure ρ₁ := hp₁.1
  let : IsProbabilityMeasure ρ₂ := hp₂.1
  have hρ₁ := regularDyadicPartMeasure_mass_one μ₁ hS₁ hμ₁ _ _ N ht₁
  have hρ₂ := regularDyadicPartMeasure_mass_one μ₂ hS₂ hμ₂ _ _ N ht₂
  have hroot := preparedRegularParts_mattila_annulus_estimate μ₁ μ₂ hθ hC
    hball₁ hball₂ hpar hconstant ht₁ ht₂ hab hS₁ hS₂
    hμ₁ hμ₂ hS₁ball hS₂ball width cutoffK
  have hCS := scheduledFourierEnergySup_le_sqrt_self ρ₁ ρ₂ S₁ S₂ E width
    (8 * T) I₁ I₂ (k₀ := 2 * T) (by omega) cutoffK N
  rw [scheduledFourierEnergySup_probability_carrier_eq ρ₁ hS₁
    measurableSet_mattila_unitSquare hρ₁ hp₁.2 E width (8 * T) I₁ I₁ (2 * T) cutoffK N,
    scheduledFourierEnergySup_probability_carrier_eq ρ₂ hS₂
      measurableSet_mattila_unitSquare hρ₂ hp₂.2 E width (8 * T)
      I₂ I₂ (2 * T) cutoffK N] at hCS
  apply hroot.trans
  simpa only [mul_assoc] using add_le_add
    (mul_le_mul_of_nonneg_left hCS (by norm_num : (0 : ℝ) ≤ 2))
    (le_refl ((2 : ℝ) ^ (-(390 * (N : ℝ)))))

end FalconerThetaGauge
