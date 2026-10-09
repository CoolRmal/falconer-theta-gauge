/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsPiecesSmooth
public import FalconerThetaGauge.MaskedMattilaRootSelfEnergy

/-! # Exact finite mixtures of the actual filtered distance measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ENNReal

namespace FalconerThetaGauge

theorem filteredCrossDistanceMeasure_restrict_carriers (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {S T : Set Plane}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (m : Plane × Plane → ℝ)
    (hm : ∀ p, p ∉ S ×ˢ T → m p = 0) :
    filteredCrossDistanceMeasure μ ν m =
      filteredCrossDistanceMeasure (μ.restrict S) (ν.restrict T) m := by
  unfold filteredCrossDistanceMeasure
  rw [Measure.prod_restrict]
  congr 1
  rw [← withDensity_indicator (hS.prod hT)]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun p ↦ by
    by_cases hp : p ∈ S ×ˢ T
    · simp only [indicator_of_mem hp]
    · simp [indicator_of_notMem hp, hm p hp]

theorem filteredCrossDistanceMeasure_congr_on_carriers (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {S T : Set Plane}
    (hS : MeasurableSet S) (hT : MeasurableSet T) {m m' : Plane × Plane → ℝ}
    (hm : ∀ x ∈ S, ∀ y ∈ T, m (x, y) = m' (x, y)) :
    filteredCrossDistanceMeasure (μ.restrict S) (ν.restrict T) m =
      filteredCrossDistanceMeasure (μ.restrict S) (ν.restrict T) m' := by
  unfold filteredCrossDistanceMeasure
  congr 1
  apply withDensity_congr_ae
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (hS.prod hT)] with p hp
  rw [hm p.1 hp.1 p.2 hp.2]

theorem filteredCrossDistanceMeasure_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Measure Plane) (ν : κ → Measure Plane)
    [∀ j, IsFiniteMeasure (ν j)] (m : Plane × Plane → ℝ) :
    filteredCrossDistanceMeasure (Measure.sum μ) (Measure.sum ν) m =
      Measure.sum (fun p : ι × κ ↦ filteredCrossDistanceMeasure (μ p.1) (ν p.2) m) := by
  unfold filteredCrossDistanceMeasure
  rw [Measure.prod_sum, withDensity_sum, Measure.map_sum continuous_dist.measurable.aemeasurable]

theorem filteredCrossDistanceMeasure_smul (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : ℝ≥0∞) (m : Plane × Plane → ℝ) :
    filteredCrossDistanceMeasure (a • μ) (b • ν) m =
      (a * b) • filteredCrossDistanceMeasure μ ν m := by
  unfold filteredCrossDistanceMeasure
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    withDensity_smul_measure, Measure.map_smul _ continuous_dist.measurable.aemeasurable]

theorem restrict_eq_mass_smul_normalizedRestrict (μ : Measure Plane)
    [IsFiniteMeasure μ] {S : Set Plane} (_hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    μ.restrict S = μ S • GaugeSeparatedMeasures.normalizedRestrict μ S := by
  unfold GaugeSeparatedMeasures.normalizedRestrict
  rw [smul_smul, ENNReal.mul_inv_cancel hpos (measure_ne_top μ S), one_smul]

/-- A disjoint finite carrier partition gives an exact mixture with the original masses. -/
theorem filteredCrossDistanceMeasure_finite_carrier_mixture
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : ι → Set Plane) (T : κ → Set Plane)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (hpS : ∀ i, μ (S i) ≠ 0) (hpT : ∀ j, ν (T j) ≠ 0)
    (m : Plane × Plane → ℝ) (mij : ι → κ → Plane × Plane → ℝ)
    (hoff : ∀ p, p ∉ (⋃ i, S i) ×ˢ (⋃ j, T j) → m p = 0)
    (hon : ∀ i j x, x ∈ S i → ∀ y, y ∈ T j → m (x, y) = mij i j (x, y)) :
    filteredCrossDistanceMeasure μ ν m = Measure.sum (fun p : ι × κ ↦
      (μ (S p.1) * ν (T p.2)) • filteredCrossDistanceMeasure
        (GaugeSeparatedMeasures.normalizedRestrict μ (S p.1))
        (GaugeSeparatedMeasures.normalizedRestrict ν (T p.2)) (mij p.1 p.2)) := by
  rw [filteredCrossDistanceMeasure_restrict_carriers μ ν
    (MeasurableSet.iUnion hS) (MeasurableSet.iUnion hT) m hoff,
    Measure.restrict_iUnion hdS hS, Measure.restrict_iUnion hdT hT,
    filteredCrossDistanceMeasure_sum]
  congr 1
  funext p
  rw [filteredCrossDistanceMeasure_congr_on_carriers μ ν (hS p.1) (hT p.2)
    (hon p.1 p.2), restrict_eq_mass_smul_normalizedRestrict μ (hS p.1) (hpS p.1),
    restrict_eq_mass_smul_normalizedRestrict ν (hT p.2) (hpT p.2)]
  let : IsProbabilityMeasure (GaugeSeparatedMeasures.normalizedRestrict μ (S p.1)) :=
    GaugeSeparatedMeasures.isProbabilityMeasure_normalizedRestrict
      (hpS p.1) (measure_ne_top μ _)
  let : IsProbabilityMeasure (GaugeSeparatedMeasures.normalizedRestrict ν (T p.2)) :=
    GaugeSeparatedMeasures.isProbabilityMeasure_normalizedRestrict
      (hpT p.2) (measure_ne_top ν _)
  exact filteredCrossDistanceMeasure_smul _ _ _ _ _

end FalconerThetaGauge
