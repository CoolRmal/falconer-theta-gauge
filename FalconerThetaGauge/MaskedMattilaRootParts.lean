/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaRootEstimate

/-! # The prepared root estimate for genuine normalized retained regular pieces -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem regularDyadicPartMeasure_mass_one (μ : Measure Plane) [IsProbabilityMeasure μ]
    {S : Set Plane} (hS : MeasurableSet S) (hμ : μ S = 1)
    (ε κ : ℝ) (N : ℕ) {t : List ℕ} (ht : t ∈ regularDyadicKeptTypes μ ε κ N) :
    regularDyadicPartMeasure μ ε N t S = 1 := by
  let ρ := regularDyadicPartMeasure μ ε N t
  let : IsProbabilityMeasure ρ := (regularDyadicPartMeasure_probability μ ε κ N ht).1
  have hnull : μ Sᶜ = 0 := by
    rw [measure_compl hS (measure_ne_top μ S), measure_univ, hμ]
    simp
  have hρnull : ρ Sᶜ = 0 := by
    change (μ (regularDyadicPartCarrier μ ε N t))⁻¹ *
      μ.restrict (regularDyadicPartCarrier μ ε N t) Sᶜ = 0
    rw [Measure.restrict_apply hS.compl]
    rw [measure_mono_null inter_subset_left hnull, mul_zero]
  have h := measure_compl hS.compl (measure_ne_top ρ Sᶜ)
  simpa only [compl_compl, measure_univ, hρnull, tsub_zero] using h

set_option maxHeartbeats 800000 in
theorem preparedRegularParts_mattila_annulus_estimate
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
    scalarFourierAnnulusIntegral
        (filteredCrossDistanceMeasure ρ₁ ρ₂ (directionalPairMask
          (ScheduledSymbolData.maskProduct.symbol ρ₁ (tolerance θ N * N) width
            (8 * expansionCount θ N) (regularMeasurePieceTests ρ₁ θ N))
          (ScheduledSymbolData.maskProduct.symbol ρ₂ (tolerance θ N * N) width
            (8 * expansionCount θ N) (regularMeasurePieceTests ρ₂ θ N))))
        ((N : ℝ) - 1) ((N : ℝ) + 1) ≤
      2 * scheduledFourierEnergySup ρ₁ ρ₂ S₁ S₂ (tolerance θ N * N) width
        (8 * expansionCount θ N) (regularMeasurePieceTests ρ₁ θ N)
        (regularMeasurePieceTests ρ₂ θ N) (2 * expansionCount θ N) cutoffK N +
      (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  let ρ₁ := regularDyadicPartMeasure μ₁ (tolerance θ N) N t₁
  let ρ₂ := regularDyadicPartMeasure μ₂ (tolerance θ N) N t₂
  let : IsProbabilityMeasure ρ₁ :=
    (regularDyadicPartMeasure_probability μ₁ (tolerance θ N) (blockParameter θ N) N ht₁).1
  let : IsProbabilityMeasure ρ₂ :=
    (regularDyadicPartMeasure_probability μ₂ (tolerance θ N) (blockParameter θ N) N ht₂).1
  have hN : 0 < N := by have := hpar.1; omega
  have hq := blockCount_pos θ hN
  have hc₁ := (regularDyadicPart_entry_properties μ₁ hθ hC hball₁ hpar hconstant ht₁).2.1
  have hc₂ := (regularDyadicPart_entry_properties μ₂ hθ hC hball₂ hpar hconstant ht₂).2.1
  have hhalf₁ : 2 * regularMeasureEntryDepth ρ₁ θ N ≤ N := by
    have h : (2 : ℝ) * regularMeasureEntryDepth ρ₁ θ N ≤ N := by linarith
    exact_mod_cast h
  have hhalf₂ : 2 * regularMeasureEntryDepth ρ₂ θ N ≤ N := by
    have h : (2 : ℝ) * regularMeasureEntryDepth ρ₂ θ N ≤ N := by linarith
    exact_mod_cast h
  apply preparedRoot_mattila_annulus_estimate hpar ρ₁ ρ₂ hab hS₁ hS₂
    (regularDyadicPartMeasure_mass_one μ₁ hS₁ hμ₁ _ _ N ht₁)
    (regularDyadicPartMeasure_mass_one μ₂ hS₂ hμ₂ _ _ N ht₂) hS₁ball hS₂ball width
    (regularMeasurePieceTests ρ₁ θ N) (regularMeasurePieceTests ρ₂ θ N)
    (profilePieceTests_card_le_scale_sq_add_one _ hpar)
    (profilePieceTests_card_le_scale_sq_add_one _ hpar) ?_ ?_ cutoffK
  · intro test ht
    exact (profilePieceTests_root_lengths hq hhalf₁ ht).1
  · intro test ht
    exact (profilePieceTests_root_lengths hq hhalf₂ ht).1

end FalconerThetaGauge
