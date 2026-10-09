module

public import FalconerThetaGauge.MaskedDistanceEnergyLevelSymbols

/-! # The genuine passing/masked/next-passing sandwich from the literal level masks -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The actual weighted pushforward using the source's literal level products. -/
def levelMaskedDistanceMeasure (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane) (E : ℝ)
    (L i K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) : Measure ℝ :=
  filteredCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y)
    (directionalPairMask
      (scheduledWidthMaskProduct ρ₁ E (directionalLevelWidth L i) K I₁)
      (scheduledWidthMaskProduct ρ₂ E (directionalLevelWidth L i) K I₂))

/-- The two structural depth orders in the actual tube and projection test records. -/
def ScheduledTestsOrdered (I : Finset ProfileScheduleTest) : Prop :=
  (∀ test ∈ I, test.kind = .tube → test.endpoint ≤ test.anchor) ∧
    (∀ test ∈ I, test.kind = .projection → test.anchor ≤ test.endpoint)

theorem ae_restricted_product_scheduledAnchorCarriers (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1) (X Y : Set Plane)
    (I₁ I₂ : Finset ProfileScheduleTest) :
    ∀ᵐ p ∂(ρ₁.restrict X).prod (ρ₂.restrict Y),
      p.1 ∈ scheduledAnchorCarrier ρ₁ I₁ ∧ p.2 ∈ scheduledAnchorCarrier ρ₂ I₂ := by
  rw [Measure.prod_restrict]
  exact ae_restrict_of_ae (ae_product_carriers ρ₁ ρ₂
    (measurableSet_scheduledAnchorCarrier ρ₁ I₁) (measurableSet_scheduledAnchorCarrier ρ₂ I₂)
    (measure_scheduledAnchorCarrier ρ₁ hρ₁ I₁) (measure_scheduledAnchorCarrier ρ₂ hρ₂ I₂))

/-- The literal passing-pair measure is dominated by the genuine level-masked measure. -/
theorem passingWeightedDistanceMeasure_le_levelMasked (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1) (X Y : Set Plane)
    (E : ℝ) (L i K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest) :
    passingWeightedDistanceMeasure ρ₁ ρ₂ X Y
        (scheduledPassingPairSet ρ₁ ρ₂ E (directionalLevelWidth L i) I₁ I₂) ≤
      levelMaskedDistanceMeasure ρ₁ ρ₂ X Y E L i K I₁ I₂ := by
  apply Measure.map_mono _ continuous_dist.measurable
  apply withDensity_mono
  filter_upwards [ae_restricted_product_scheduledAnchorCarriers ρ₁ ρ₂ hρ₁ hρ₂ X Y I₁ I₂]
    with p hp
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  by_cases hz : p ∈ scheduledPassingPairSet ρ₁ ρ₂ E (directionalLevelWidth L i) I₁ I₂
  · obtain ⟨hp₁, hp₂⟩ := (mem_scheduledPassingPairSet_iff _ _ _ _ _ _ _).1 hz
    rw [indicator_of_mem hz, directionalPairMask,
      scheduledWidthMaskProduct_eq_one_of_passing ρ₁ E _ K I₁ hp.1 _ hp₁,
      scheduledWidthMaskProduct_eq_one_of_passing ρ₂ E _ K I₂ hp.2 _ hp₂, one_mul]
  · rw [indicator_of_notMem hz]
    exact (directionalPairMask_mem_Icc
      (scheduledWidthMaskProduct_mem_Icc ρ₁ E _ K I₁)
      (scheduledWidthMaskProduct_mem_Icc ρ₂ E _ K I₂) p).1

/-- L2 for the literal tests proves that the true masked measure is dominated by next passing. -/
theorem levelMaskedDistanceMeasure_le_nextPassing (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1) (X Y : Set Plane)
    (E : ℝ) {L : ℕ} (hL : 0 < L) (hsize : (L : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K : ℕ) (I₁ I₂ : Finset ProfileScheduleTest)
    (hordered₁ : ScheduledTestsOrdered I₁) (hordered₂ : ScheduledTestsOrdered I₂) :
    levelMaskedDistanceMeasure ρ₁ ρ₂ X Y E L i K I₁ I₂ ≤
      passingWeightedDistanceMeasure ρ₁ ρ₂ X Y
        (scheduledPassingPairSet ρ₁ ρ₂ E (directionalLevelWidth L (i + 1)) I₁ I₂) := by
  apply Measure.map_mono _ continuous_dist.measurable
  apply withDensity_mono
  filter_upwards [ae_restricted_product_scheduledAnchorCarriers ρ₁ ρ₂ hρ₁ hρ₂ X Y I₁ I₂]
    with p hp
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  by_cases hz : p ∈ scheduledPassingPairSet ρ₁ ρ₂ E (directionalLevelWidth L (i + 1)) I₁ I₂
  · rw [indicator_of_mem hz]
    exact (directionalPairMask_mem_Icc
      (scheduledWidthMaskProduct_mem_Icc ρ₁ E _ K I₁)
      (scheduledWidthMaskProduct_mem_Icc ρ₂ E _ K I₂) p).2
  · have hzero : directionalPairMask
        (scheduledWidthMaskProduct ρ₁ E (directionalLevelWidth L i) K I₁)
        (scheduledWidthMaskProduct ρ₂ E (directionalLevelWidth L i) K I₂) p = 0 := by
      by_contra hn
      have hprod := mul_ne_zero_iff.1 hn
      apply hz
      apply (mem_scheduledPassingPairSet_iff _ _ _ _ _ _ _).2
      exact ⟨scheduledWidthMaskProduct_ne_zero_implies_next_passing ρ₁ E hL hsize i K I₁
          hordered₁.1 hordered₁.2 hp.1 _ hprod.1,
        scheduledWidthMaskProduct_ne_zero_implies_next_passing ρ₂ E hL hsize i K I₂
          hordered₂.1 hordered₂.2 hp.2 _ hprod.2⟩
    simp only [hzero, indicator_of_notMem hz, le_refl]

end FalconerThetaGauge
