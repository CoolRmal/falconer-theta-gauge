module

public import FalconerThetaGauge.RadialProjectionLimitPrepared
public import FalconerThetaGauge.OrthogonalProjectionRadialEstimate

/-!
# Uniform radial Orlicz bounds for the prepared source approximation

The actual tiny smooth sources retain the distance bound one. Polar rays
are bounded by their orthogonal line integrals; the proved orthogonal
quadratic estimate and the Orlicz product inequality control those line
integrals against the actual singular pin projections. Convolution decreases
Fourier energy, so the resulting constant is independent of the bump index.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The literal polar-ray density of every prepared approximation satisfies a
uniform Orlicz bound proved from the original source and pin Fourier energies. -/
theorem lintegral_orlicz_smooth_radial_le
    (μ ν : ProbabilityMeasure Plane) {a b : Plane} (hab : dist a b = 1 / 4)
    (hμ : ∀ᵐ x ∂(μ : Measure Plane), dist x a ≤ 1 / 400)
    (hν : ∀ᵐ y ∂(ν : Measure Plane), dist y b ≤ 1 / 400)
    (γ : ℝ) (hγ : 1 ≤ γ)
    (hμenergy : logarithmicFourierEnergy γ (μ : Measure Plane) ≠ ∞)
    (hνenergy : logarithmicFourierEnergy γ (ν : Measure Plane) ≠ ∞) (n : ℕ) :
    (∫⁻ x, ∫⁻ w, orliczPhiExtended γ
      (circleRayDensity (fun y ↦ ENNReal.ofReal (smoothMeasureDensity (ν : Measure Plane)
        ((shrinkingRadialBump n).normed volume) y)) x w)
      ∂circleArcLength ∂(μ : Measure Plane)) ≤
      ENNReal.ofReal (2 * orthogonalOrliczLineConstant γ) *
        (logarithmicFourierEnergy γ (ν : Measure Plane) +
          logarithmicFourierEnergy γ (μ : Measure Plane)) := by
  let φ := shrinkingRadialBump n
  let f : Plane → ℝ≥0∞ := fun y ↦
    ENNReal.ofReal (smoothMeasureDensity (ν : Measure Plane) (φ.normed volume) y)
  have hf : Measurable f :=
    (contDiff_smoothMeasureDensity (ν : Measure Plane) φ.contDiff_normed
      φ.hasCompactSupport_normed).continuous.measurable.ennreal_ofReal
  have hde : volume.withDensity f = (smoothSourceProbability ν φ : Measure Plane) :=
    withDensity_smoothMeasureDensity_eq_conv ν φ.contDiff_normed
      φ.hasCompactSupport_normed φ.nonneg_normed
  have : IsProbabilityMeasure (volume.withDensity f) := hde ▸ inferInstance
  have hcontract : logarithmicFourierEnergy γ (volume.withDensity f) ≤
      logarithmicFourierEnergy γ (ν : Measure Plane) := by
    rw [hde]
    exact logarithmicFourierEnergy_smoothSourceProbability_le γ ν φ
  have hfenergy : logarithmicFourierEnergy γ (volume.withDensity f) ≠ ∞ :=
    ne_top_of_le_ne_top hνenergy hcontract
  have hdist : ∀ᵐ x ∂(μ : Measure Plane), ∀ y, f y ≠ 0 → dist x y ≤ 1 :=
    ae_dist_le_one_of_smooth_density_ne_zero μ ν hab hμ hν n
  have hrad := lintegral_circleRayDensity_orlicz_le_orthogonal hf (μ : Measure Plane)
    (zero_le_one.trans hγ) (D := 1) le_rfl hdist
  have hprod := lintegral_orliczPhi_angularLineDensity_pinProjection_le hf
    (μ : Measure Plane) γ hγ hfenergy hμenergy
  calc
    _ ≤ (∫⁻ θ, ∫⁻ t : ℝ, orliczPhiExtended γ
        (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
        ∂(μ : Measure Plane).map (fun x ↦ inner ℝ x (angularDirection (θ - Real.pi / 2)))
        ∂radialAngularMeasure) := by
      simpa only [Real.log_one, add_zero, Real.one_rpow, one_mul,
        ENNReal.ofReal_one] using hrad
    _ ≤ ENNReal.ofReal (2 * orthogonalOrliczLineConstant γ) *
        (logarithmicFourierEnergy γ (volume.withDensity f) +
          logarithmicFourierEnergy γ (μ : Measure Plane)) := hprod
    _ ≤ _ := by gcongr

end FalconerThetaGauge
