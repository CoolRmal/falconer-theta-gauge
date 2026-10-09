module

public import FalconerThetaGauge.RadialProjectionLimitEndpoint
public import FalconerThetaGauge.RadialProjectionLimitConvergence

/-!
# Passage from smooth radial bounds to the actual radial endpoint

The approximating source measures are actual Lebesgue densities. Their exact
polar ray densities satisfy a stronger uniform moment bound; source weak
convergence and separation identify their joint limit with the original
radial pushforward. This yields its actual almost-everywhere density and the
requested lower moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The concrete weak-limit step: actual smooth source densities and uniform
stronger polar-ray bounds yield the actual endpoint radial densities. -/
theorem ae_radialProjection_orlicz_density_of_approximating_sources
    (μ ν : ProbabilityMeasure Plane) {νn : ℕ → ProbabilityMeasure Plane}
    (hconv : Tendsto νn atTop (𝓝 ν)) {K L : Set Plane}
    (hK : IsClosed K) (hL : IsClosed L)
    (hμ : (μ : Measure Plane) Kᶜ = 0) (hν : (ν : Measure Plane) Lᶜ = 0)
    (hνn : ∀ n, (νn n : Measure Plane) Lᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ x ∈ K, ∀ y ∈ L, s ≤ dist x y)
    {fn : ℕ → Plane → ℝ≥0∞} (hfn : ∀ n, Measurable (fn n))
    (hdensity : ∀ n, (νn n : Measure Plane) = volume.withDensity (fn n))
    {γ : ℝ} (hγ : 0 ≤ γ) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hbound : ∀ n, (∫⁻ x, ∫⁻ w, orliczPhiExtended (γ + 2)
      (circleRayDensity (fn n) x w) ∂circleArcLength ∂(μ : Measure Plane)) ≤ B) :
    ∀ᵐ x ∂(μ : Measure Plane), (ν : Measure Plane).map (radialProjection x) ≪ circleArcLength ∧
      circleArcLength.withDensity (radialProjectionDensity (ν : Measure Plane) x) =
        (ν : Measure Plane).map (radialProjection x) ∧
      (∫⁻ w, orliczPhiExtended γ (radialProjectionDensity (ν : Measure Plane) x w)
        ∂circleArcLength) ≠ ∞ := by
  let ξ : Measure (Plane × UnitCircle) := (μ : Measure Plane).prod circleArcLength
  have hjconv := tendsto_jointRadialProbability_of_separated μ ν hconv hK hL hμ hν hνn hs hsep
  have hjdensity : ∀ n, (jointRadialProbability μ (νn n) : Measure (Plane × UnitCircle)) =
      ξ.withDensity (fun p ↦ circleRayDensity (fn n) p.1 p.2) := by
    intro n
    have : IsFiniteMeasure (volume.withDensity (fn n)) := hdensity n ▸ inferInstance
    rw [coe_jointRadialProbability, hdensity n]
    exact jointRadialMeasure_withDensity_eq μ (hfn n)
  have hjbound : ∀ n, (∫⁻ p, orliczPhiExtended (γ + 2)
      (circleRayDensity (fn n) p.1 p.2) ∂ξ) ≤ B := by
    intro n
    rw [show ξ = (μ : Measure Plane).prod circleArcLength from rfl, lintegral_prod _ (by fun_prop)]
    exact hbound n
  obtain ⟨hac, henergy⟩ := weak_limit_orlicz_density ξ hγ hB hjdensity hjbound hjconv
  exact ae_radialProjection_orlicz_density_of_joint μ ν hac henergy

end FalconerThetaGauge
