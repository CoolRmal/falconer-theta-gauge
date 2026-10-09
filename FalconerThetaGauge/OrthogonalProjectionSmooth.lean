module

public import FalconerThetaGauge.OrthogonalProjectionAngular
public import FalconerThetaGauge.SmoothProbabilityApproximation

/-!
# Uniform Orlicz estimates for genuine smooth source approximations

The explicit line density of convolution with a normalized compact smooth bump
obeys the same averaged quadratic Orlicz bound at every approximation scale.
The right side involves only the original source's literal weighted Fourier energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Convolution

namespace FalconerThetaGauge

/-- The exact perpendicular-frame bound is uniform in every normalized smooth bump. -/
theorem lintegral_orliczQuadratic_smooth_angularLineDensity_le
    (μ : Measure Plane) [IsProbabilityMeasure μ] (φ : ContDiffBump (0 : Plane))
    (γ : ℝ) (hγ : 1 ≤ γ) (henergy : logarithmicFourierEnergy γ μ ≠ ∞) :
    (∫⁻ θ, ∫⁻ t : ℝ, orliczQuadraticExtended γ
      (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2))
        (fun y ↦ ENNReal.ofReal (smoothMeasureDensity μ (φ.normed volume) y)) t)
      ∂volume ∂radialAngularMeasure) ≤
      ENNReal.ofReal (2 * orthogonalOrliczLineConstant γ) * logarithmicFourierEnergy γ μ := by
  let f : Plane → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (smoothMeasureDensity μ (φ.normed volume) y)
  have hf : Measurable f :=
    (contDiff_smoothMeasureDensity μ φ.contDiff_normed φ.hasCompactSupport_normed).continuous.measurable.ennreal_ofReal
  have := isProbabilityMeasure_smoothMeasureDensity μ φ
  have hE : logarithmicFourierEnergy γ (volume.withDensity f) ≤ logarithmicFourierEnergy γ μ := by
    rw [show volume.withDensity f = μ ∗ smoothBumpMeasure φ from
      withDensity_smoothMeasureDensity_eq_conv μ φ.contDiff_normed
        φ.hasCompactSupport_normed φ.nonneg_normed]
    exact logarithmicFourierEnergy_conv_le γ μ _
  exact (lintegral_orliczQuadratic_angularLineDensity_le hf γ hγ
    (ne_top_of_le_ne_top henergy hE)).trans (mul_le_mul' le_rfl hE)

end FalconerThetaGauge
