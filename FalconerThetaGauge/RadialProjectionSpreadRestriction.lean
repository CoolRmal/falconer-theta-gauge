module

public import FalconerThetaGauge.RadialProjectionSpreadGoodPins

/-!
# Actual retained probabilities and their uniform radial bounds

Quarter-mass compact restrictions are normalized to genuine probabilities.
Their carriers, supports, and gauge bounds are retained explicitly. The
actual radial pushforward at every retained good pin has its canonical
density and a uniformly scaled logarithmic Orlicz moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures in
/-- The actual normalized probability retained on a quarter-mass set. -/
def retainedRadialProbability (μ : ProbabilityMeasure Plane) (A : Set Plane)
    (hmass : (1 / 4 : ℝ≥0∞) ≤ (μ : Measure Plane) A) : ProbabilityMeasure Plane :=
  ⟨normalizedRestrict (μ : Measure Plane) A,
    isProbabilityMeasure_normalizedRestrict
      ((by norm_num : (0 : ℝ≥0∞) < 1 / 4).trans_le hmass).ne'
      (measure_ne_top _ _)⟩

open GaugeSeparatedMeasures in
@[simp]
theorem coe_retainedRadialProbability (μ : ProbabilityMeasure Plane) (A : Set Plane)
    (hmass : (1 / 4 : ℝ≥0∞) ≤ (μ : Measure Plane) A) :
    (retainedRadialProbability μ A hmass : Measure Plane) = normalizedRestrict (μ : Measure Plane) A :=
  rfl

theorem retainedRadialProbability_le_four (μ : ProbabilityMeasure Plane) (A : Set Plane)
    (hmass : (1 / 4 : ℝ≥0∞) ≤ (μ : Measure Plane) A) :
    (retainedRadialProbability μ A hmass : Measure Plane) ≤ (4 : ℝ≥0∞) • (μ : Measure Plane) :=
  normalizedRestrict_le_four μ hmass

theorem retainedRadialProbability_carrier (μ : ProbabilityMeasure Plane) {A : Set Plane}
    (hA : IsCompact A) (hmass : (1 / 4 : ℝ≥0∞) ≤ (μ : Measure Plane) A) :
    (retainedRadialProbability μ A hmass : Measure Plane) A = 1 ∧
      (retainedRadialProbability μ A hmass : Measure Plane).support ⊆ A := by
  refine ⟨(prob_compl_eq_zero_iff hA.measurableSet).mp ?_,
    GaugeSeparatedMeasures.normalizedRestrict_support_subset hA.isClosed⟩
  exact GaugeSeparatedMeasures.normalizedRestrict_compl hA.measurableSet

/-- The retained probability has the same gauge with a uniformly quadrupled constant. -/
theorem hasGaugeBallBound_retainedRadialProbability (μ : ProbabilityMeasure Plane) {A : Set Plane}
    (hmass : (1 / 4 : ℝ≥0∞) ≤ (μ : Measure Plane) A) {θ C : ℝ}
    (hball : HasGaugeBallBound (μ : Measure Plane) θ C) :
    HasGaugeBallBound (retainedRadialProbability μ A hmass : Measure Plane) θ (4 * C) := by
  intro x r hr hr1
  calc
    _ ≤ (4 : ℝ≥0∞) * (μ : Measure Plane) (Metric.ball x r) :=
      retainedRadialProbability_le_four μ A hmass _
    _ ≤ (4 : ℝ≥0∞) * (ENNReal.ofReal C * ENNReal.ofReal (realGauge θ r)) :=
      mul_le_mul' le_rfl (hball x r hr hr1)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_ofNat, mul_assoc]

/-- At every individual good pin, the canonical density reconstructs the actual radial measure. -/
theorem radialProjection_withDensity_eq (ν : Measure Plane) [IsFiniteMeasure ν] (x : Plane)
    (hac : ν.map (radialProjection x) ≪ circleArcLength) :
    circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) := by
  have h := Kernel.withDensity_rnDeriv_eq
    (κ := radialProjectionKernel ν) (η := Kernel.const Plane circleArcLength) hac
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _)] at h
  exact h

/-- Every specified good pin retains a genuine uniformly controlled radial density
when the source is restricted and normalized. -/
theorem radialProjection_retained_density_bound
    (ν : ProbabilityMeasure Plane) {A : Set Plane}
    (hmass : (1 / 4 : ℝ≥0∞) ≤ (ν : Measure Plane) A) (x : Plane)
    (hac : (ν : Measure Plane).map (radialProjection x) ≪ circleArcLength)
    {γ K : ℝ} (hγ : 0 ≤ γ)
    (hbound : radialOrliczMoment (ν : Measure Plane) γ x ≤ ENNReal.ofReal K) :
    (retainedRadialProbability ν A hmass : Measure Plane).map (radialProjection x) ≪ circleArcLength ∧
      circleArcLength.withDensity
        (radialProjectionDensity (retainedRadialProbability ν A hmass : Measure Plane) x) =
        (retainedRadialProbability ν A hmass : Measure Plane).map (radialProjection x) ∧
      radialOrliczMoment (retainedRadialProbability ν A hmass : Measure Plane) γ x ≤
        ENNReal.ofReal (4 * (1 + Real.log 4) ^ γ) * ENNReal.ofReal K := by
  have hle := retainedRadialProbability_le_four ν A hmass
  have hac' := (radialProjection_density_le_four _ _ hle x hac).1
  refine ⟨hac', radialProjection_withDensity_eq _ x hac', ?_⟩
  exact (lintegral_radialProjection_orlicz_le_four _ _ hle x hac hγ).trans
    (mul_le_mul' le_rfl hbound)

end FalconerThetaGauge
