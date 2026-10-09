module

public import FalconerThetaGauge.RadialProjectionUniformBound
public import FalconerThetaGauge.RadialProjectionLimitAssembly

/-!
# Actual radial endpoint for the gauge Frostman preparation

The genuine prepared source measures have logarithmic energies at every
order. A bound two logarithmic powers stronger than the requested order
gives uniform absolute continuity of their joint smooth radial distributions.
The proved weak-limit argument yields the actual circle pushforward density,
including its finite requested Orlicz moment, almost everywhere in the pin.
This route uses no additional hypothesis on the target compact set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The actual endpoint density for prepared probabilities. The source's
two spare logarithmic powers are supplied by the gauge Frostman estimates. -/
theorem ae_radialProjection_orlicz_density_prepared
    (μ ν : ProbabilityMeasure Plane) {a b : Plane} (hab : dist a b = 1 / 4)
    (hμ : ∀ᵐ x ∂(μ : Measure Plane), dist x a ≤ 1 / 400)
    (hν : ∀ᵐ y ∂(ν : Measure Plane), dist y b ≤ 1 / 400)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hμenergy : logarithmicFourierEnergy (γ + 2) (μ : Measure Plane) ≠ ∞)
    (hνenergy : logarithmicFourierEnergy (γ + 2) (ν : Measure Plane) ≠ ∞) :
    ∀ᵐ x ∂(μ : Measure Plane), (ν : Measure Plane).map (radialProjection x) ≪ circleArcLength ∧
      circleArcLength.withDensity (radialProjectionDensity (ν : Measure Plane) x) =
        (ν : Measure Plane).map (radialProjection x) ∧
      (∫⁻ w, orliczPhiExtended γ (radialProjectionDensity (ν : Measure Plane) x w)
        ∂circleArcLength) ≠ ∞ := by
  let νn : ℕ → ProbabilityMeasure Plane := fun n ↦ smoothSourceProbability ν (shrinkingRadialBump n)
  let fn : ℕ → Plane → ℝ≥0∞ := fun n y ↦ ENNReal.ofReal
    (smoothMeasureDensity (ν : Measure Plane) ((shrinkingRadialBump n).normed volume) y)
  let B : ℝ≥0∞ := ENNReal.ofReal (2 * orthogonalOrliczLineConstant (γ + 2)) *
    (logarithmicFourierEnergy (γ + 2) (ν : Measure Plane) +
      logarithmicFourierEnergy (γ + 2) (μ : Measure Plane))
  have hB : B ≠ ∞ := by dsimp only [B]; finiteness
  have hpin : (μ : Measure Plane) (Metric.closedBall a (1 / 400))ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hμ] with x hx
    exact Metric.mem_closedBall.mpr hx
  have hfn : ∀ n, Measurable (fn n) := fun n ↦
    (contDiff_smoothMeasureDensity (ν : Measure Plane) (shrinkingRadialBump n).contDiff_normed
      (shrinkingRadialBump n).hasCompactSupport_normed).continuous.measurable.ennreal_ofReal
  have hdensity : ∀ n, (νn n : Measure Plane) = volume.withDensity (fn n) := by
    intro n
    exact (withDensity_smoothMeasureDensity_eq_conv ν (shrinkingRadialBump n).contDiff_normed
      (shrinkingRadialBump n).hasCompactSupport_normed (shrinkingRadialBump n).nonneg_normed).symm
  apply ae_radialProjection_orlicz_density_of_approximating_sources μ ν
    (tendsto_radial_smoothSourceProbability ν) Metric.isClosed_closedBall Metric.isClosed_closedBall
    hpin (radial_source_compl_carrier ν b hν) (radial_smoothed_source_compl_carrier ν b hν)
    (s := 1 / 5) (by norm_num)
    (fun x hx y hy ↦ (prepared_enlarged_balls_distance_bounds hab hx hy).1)
    hfn hdensity hγ hB
  intro n
  exact lintegral_orlicz_smooth_radial_le μ ν hab hμ hν (γ + 2) (by linarith)
    hμenergy hνenergy n

end FalconerThetaGauge
