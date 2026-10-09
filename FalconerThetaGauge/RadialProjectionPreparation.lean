module

public import FalconerThetaGauge.RadialProjectionEndpoint

/-!
# Gauge Frostman preparation with actual radial Orlicz densities

Starting only from positive gauge Hausdorff measure of the compact target,
the actual similar copy contains the two prepared compact probability
carriers. Every logarithmic spatial/Fourier energy is finite, and the actual
radial pushforward between the carriers has an Orlicz density of every
requested logarithmic order almost everywhere in either pin measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures in
/-- The concrete gauge preparation, including the genuine radial density and
Orlicz conclusions. The endpoint is obtained without an extra target hypothesis. -/
theorem exists_prepared_probabilityMeasures_radial_orlicz {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) {E : Set Plane} (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) :
    ∃ (ℓ C : ℝ) (z a b : Plane) (S₁ S₂ : Set Plane)
      (μ₁ μ₂ : ProbabilityMeasure Plane),
      0 < ℓ ∧ 0 < C ∧ IsCompact S₁ ∧ IsCompact S₂ ∧
      S₁ ⊆ affineMap ℓ z '' E ∧ S₂ ⊆ affineMap ℓ z '' E ∧
      (μ₁ : Measure Plane) S₁ = 1 ∧ (μ₂ : Measure Plane) S₂ = 1 ∧
      (μ₁ : Measure Plane).support ⊆ S₁ ∧ (μ₂ : Measure Plane).support ⊆ S₂ ∧
      dist a b = 1 / 4 ∧
      S₁ ⊆ Metric.ball a (1 / 400) ∧ S₂ ⊆ Metric.ball b (1 / 400) ∧
      Metric.ball a (1 / 400) ⊆ unitSquare ∧ Metric.ball b (1 / 400) ⊆ unitSquare ∧
      (∀ x ∈ S₁, ∀ y ∈ S₂,
        (24 / 100 : ℝ) ≤ dist x y ∧ dist x y ≤ (26 / 100 : ℝ)) ∧
      HasGaugeBallBound (μ₁ : Measure Plane) θ C ∧ HasGaugeBallBound (μ₂ : Measure Plane) θ C ∧
      ∀ γ : ℝ, 1 ≤ γ →
        logCriticalEnergy γ (μ₁ : Measure Plane) ≠ ∞ ∧
        logCriticalEnergy γ (μ₂ : Measure Plane) ≠ ∞ ∧
        logarithmicFourierEnergy γ (μ₁ : Measure Plane) ≠ ∞ ∧
        logarithmicFourierEnergy γ (μ₂ : Measure Plane) ≠ ∞ ∧
        (∀ᵐ x ∂(μ₁ : Measure Plane),
          (μ₂ : Measure Plane).map (radialProjection x) ≪ circleArcLength ∧
          circleArcLength.withDensity (radialProjectionDensity (μ₂ : Measure Plane) x) =
            (μ₂ : Measure Plane).map (radialProjection x) ∧
          (∫⁻ w, orliczPhiExtended γ (radialProjectionDensity (μ₂ : Measure Plane) x w)
            ∂circleArcLength) ≠ ∞) ∧
        (∀ᵐ y ∂(μ₂ : Measure Plane),
          (μ₁ : Measure Plane).map (radialProjection y) ≪ circleArcLength ∧
          circleArcLength.withDensity (radialProjectionDensity (μ₁ : Measure Plane) y) =
            (μ₁ : Measure Plane).map (radialProjection y) ∧
          (∫⁻ w, orliczPhiExtended γ (radialProjectionDensity (μ₁ : Measure Plane) y w)
            ∂circleArcLength) ≠ ∞) := by
  obtain ⟨ℓ, C, z, a, b, S₁, S₂, μ₁, μ₂, hℓ, hC, hS₁, hS₂, hsub₁, hsub₂,
    hmass₁, hmass₂, hsupport₁, hsupport₂, hab, hball₁, hball₂, hsq₁, hsq₂,
    hsep, hgb₁, hgb₂, henergy⟩ :=
    exists_prepared_probabilityMeasures_finite_logCriticalEnergy hθ₀ hθ₁ hE hGauge
  have hd₁ := ae_dist_le_of_compact_carrier μ₁ hS₁ hmass₁ hball₁
  have hd₂ := ae_dist_le_of_compact_carrier μ₂ hS₂ hmass₂ hball₂
  refine ⟨ℓ, C, z, a, b, S₁, S₂, μ₁, μ₂, hℓ, hC, hS₁, hS₂, hsub₁, hsub₂,
    hmass₁, hmass₂, hsupport₁, hsupport₂, hab, hball₁, hball₂, hsq₁, hsq₂,
    hsep, hgb₁, hgb₂, ?_⟩
  intro γ hγ
  have hγ₀ : 0 ≤ γ := zero_le_one.trans hγ
  have hp : 1 ≤ γ + 2 := by linarith
  have hfp₁ := logarithmicFourierEnergy_ne_top (γ + 2) (by linarith) (μ₁ : Measure Plane)
    (henergy (γ + 2) hp).1
  have hfp₂ := logarithmicFourierEnergy_ne_top (γ + 2) (by linarith) (μ₂ : Measure Plane)
    (henergy (γ + 2) hp).2
  exact ⟨(henergy γ hγ).1, (henergy γ hγ).2,
    logarithmicFourierEnergy_ne_top γ hγ₀ (μ₁ : Measure Plane) (henergy γ hγ).1,
    logarithmicFourierEnergy_ne_top γ hγ₀ (μ₂ : Measure Plane) (henergy γ hγ).2,
    ae_radialProjection_orlicz_density_prepared μ₁ μ₂ hab hd₁ hd₂ γ hγ₀ hfp₁ hfp₂,
    ae_radialProjection_orlicz_density_prepared μ₂ μ₁ (by simpa only [dist_comm] using hab)
      hd₂ hd₁ γ hγ₀ hfp₂ hfp₁⟩

end FalconerThetaGauge
