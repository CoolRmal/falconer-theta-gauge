module

public import FalconerThetaGauge.RadialProjectionLimitJoint
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Identification of the actual radial densities

Joint absolute continuity implies absolute continuity of the real radial
pushforward for almost every pin. Its joint Radon–Nikodym moment identifies
the actual kernel density and gives the almost-everywhere Orlicz conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- Joint absolute continuity is absolute continuity of actual radial measures
at almost every pin. -/
theorem ae_radialProjection_absolutelyContinuous_of_joint (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : jointRadialMeasure μ ν ≪ μ.prod circleArcLength) :
    ∀ᵐ x ∂μ, ν.map (radialProjection x) ≪ circleArcLength := by
  rw [jointRadialMeasure_eq_compProd, ← Measure.compProd_const] at hac
  exact hac.kernel_of_compProd

/-- The density is the previously defined genuine radial kernel derivative,
and reconstructs the actual radial pushforward. -/
theorem ae_radialProjection_density_of_joint (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : jointRadialMeasure μ ν ≪ μ.prod circleArcLength) :
    ∀ᵐ x ∂μ, circleArcLength.withDensity (radialProjectionDensity ν x) =
      ν.map (radialProjection x) := by
  filter_upwards [ae_radialProjection_absolutelyContinuous_of_joint μ ν hac] with x hx
  have h := Kernel.withDensity_rnDeriv_eq
    (κ := radialProjectionKernel ν) (η := Kernel.const Plane circleArcLength) hx
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _)] at h
  exact h

/-- A finite joint moment gives a finite genuine radial Orlicz moment at almost every pin. -/
theorem ae_lintegral_orlicz_radialProjectionDensity_ne_top_of_joint
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {γ : ℝ}
    (henergy : (∫⁻ p, orliczPhiExtended γ
      ((jointRadialMeasure μ ν).rnDeriv (μ.prod circleArcLength) p)
        ∂(μ.prod circleArcLength)) ≠ ∞) :
    ∀ᵐ x ∂μ, (∫⁻ w, orliczPhiExtended γ (radialProjectionDensity ν x w)
      ∂circleArcLength) ≠ ∞ := by
  have heq : (∫⁻ p, orliczPhiExtended γ
      ((jointRadialMeasure μ ν).rnDeriv (μ.prod circleArcLength) p)
        ∂(μ.prod circleArcLength)) =
      ∫⁻ x, ∫⁻ w, orliczPhiExtended γ (radialProjectionDensity ν x w)
        ∂circleArcLength ∂μ := by
    calc
      _ = ∫⁻ p, orliczPhiExtended γ (radialProjectionDensity ν p.1 p.2)
          ∂(μ.prod circleArcLength) := by
        apply lintegral_congr_ae
        filter_upwards [jointRadialMeasure_rnDeriv_ae_eq μ ν] with p hp
        rw [hp]
      _ = _ := lintegral_prod _ (by fun_prop)
  rw [heq] at henergy
  have hmeas : Measurable (fun x ↦ ∫⁻ w,
      orliczPhiExtended γ (radialProjectionDensity ν x w) ∂circleArcLength) := by
    fun_prop
  filter_upwards [ae_lt_top hmeas henergy] with x hx
  exact hx.ne

/-- The actual endpoint conclusion follows from the actual joint limit density. -/
theorem ae_radialProjection_orlicz_density_of_joint
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {γ : ℝ}
    (hac : jointRadialMeasure μ ν ≪ μ.prod circleArcLength)
    (henergy : (∫⁻ p, orliczPhiExtended γ
      ((jointRadialMeasure μ ν).rnDeriv (μ.prod circleArcLength) p)
        ∂(μ.prod circleArcLength)) ≠ ∞) :
    ∀ᵐ x ∂μ, ν.map (radialProjection x) ≪ circleArcLength ∧
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      (∫⁻ w, orliczPhiExtended γ (radialProjectionDensity ν x w) ∂circleArcLength) ≠ ∞ := by
  filter_upwards [ae_radialProjection_absolutelyContinuous_of_joint μ ν hac,
    ae_radialProjection_density_of_joint μ ν hac,
    ae_lintegral_orlicz_radialProjectionDensity_ne_top_of_joint μ ν henergy] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩

end FalconerThetaGauge
