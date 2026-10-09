module

public import FalconerThetaGauge.OrthogonalProjectionSmooth

/-!
# The genuine smooth radial Orlicz estimate

The actual pin projection is absolutely continuous at almost every direction by
the proved Fourier projection theorem. Its jointly measurable density converts
the radial full-line estimate to the elementary Orlicz product inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Convolution

namespace FalconerThetaGauge

theorem map_shifted_angular_eq_circle :
    radialAngularMeasure.map (fun θ ↦ unitCircleOfAngle (θ - Real.pi / 2)) = circleArcLength := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf (by fun_prop)]
  exact lintegral_shifted_angular_eq_circle hf

theorem ae_memLp_shifted_orthogonalProjection (γ : ℝ) (hγ : 0 ≤ γ)
    (ν : Measure Plane) [IsProbabilityMeasure ν] (henergy : logarithmicFourierEnergy γ ν ≠ ∞) :
    ∀ᵐ θ ∂radialAngularMeasure,
      MemLp (charFun (orthogonalProjectionMeasure ν (angularDirection (θ - Real.pi / 2))))
        2 volume := by
  have h := ae_memLp_charFun_orthogonalProjection_circle γ hγ ν henergy
  rw [← map_shifted_angular_eq_circle] at h
  have hmap : AEMeasurable (fun θ ↦ unitCircleOfAngle (θ - Real.pi / 2))
      radialAngularMeasure := (by fun_prop : Measurable
        (fun θ ↦ unitCircleOfAngle (θ - Real.pi / 2))).aemeasurable
  exact ae_of_ae_map hmap h

theorem withDensity_orthogonalProjectionDensity_of_memLp
    (ν : Measure Plane) [IsProbabilityMeasure ν] (w : UnitCircle)
    (hw : MemLp (charFun (orthogonalProjectionMeasure ν (w : Plane))) 2 volume) :
    orthogonalProjectionMeasure ν (w : Plane) = volume.withDensity
      (fun t ↦ ENNReal.ofReal (orthogonalProjectionDensity ν w t)) := by
  exact (withDensity_kernelDensity (orthogonalProjectionKernel ν) volume
    (a := w) (by simpa only [orthogonalProjectionKernel_apply] using
      absolutelyContinuous_of_memLp_charFun _ hw)).symm

/-- The literal line integral against the actual pin projection is controlled by
the two averaged quadratic Orlicz integrals. -/
theorem lintegral_orliczPhi_angularLineDensity_pinProjection_le
    {f : Plane → ℝ≥0∞} (hf : Measurable f) [IsProbabilityMeasure (volume.withDensity f)]
    (ν : Measure Plane) [IsProbabilityMeasure ν] (γ : ℝ) (hγ : 1 ≤ γ)
    (hfenergy : logarithmicFourierEnergy γ (volume.withDensity f) ≠ ∞)
    (hνenergy : logarithmicFourierEnergy γ ν ≠ ∞) :
    (∫⁻ θ, ∫⁻ t : ℝ, orliczPhiExtended γ
      (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
      ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫) ∂radialAngularMeasure) ≤
      ENNReal.ofReal (2 * orthogonalOrliczLineConstant γ) *
        (logarithmicFourierEnergy γ (volume.withDensity f) + logarithmicFourierEnergy γ ν) := by
  have ha : ∀ᵐ θ ∂radialAngularMeasure,
      (∫⁻ t : ℝ, orliczPhiExtended γ
        (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
        ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫)) ≤
      (∫⁻ t : ℝ, orliczQuadraticExtended γ
        (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)) +
      ∫⁻ t : ℝ, orliczQuadraticENN γ
        (orthogonalProjectionDensity ν (unitCircleOfAngle (θ - Real.pi / 2)) t) := by
    filter_upwards [ae_memLp_shifted_orthogonalProjection γ (zero_le_one.trans hγ) ν hνenergy]
      with θ hθ
    let w := unitCircleOfAngle (θ - Real.pi / 2)
    have hd := withDensity_orthogonalProjectionDensity_of_memLp ν w hθ
    change ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫) = _ at hd
    rw [hd]
    have hprod := lintegral_orliczPhiExtended_withDensity_le volume
      (measurable_orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) hf)
      (b := fun t ↦ ENNReal.ofReal (orthogonalProjectionDensity ν w t))
      (by fun_prop) (zero_le_one.trans hγ)
    have hQ (t : ℝ) : orliczQuadraticExtended γ
        (ENNReal.ofReal (orthogonalProjectionDensity ν w t)) =
        orliczQuadraticENN γ (orthogonalProjectionDensity ν w t) :=
      orliczQuadraticExtended_ofReal γ (orthogonalProjectionDensity_nonneg ν w t)
    simpa only [hQ] using hprod
  have hQf := lintegral_orliczQuadratic_angularLineDensity_le hf γ hγ hfenergy
  have hQν : (∫⁻ θ, ∫⁻ t : ℝ, orliczQuadraticENN γ
      (orthogonalProjectionDensity ν (unitCircleOfAngle (θ - Real.pi / 2)) t)
      ∂volume ∂radialAngularMeasure) ≤
      ENNReal.ofReal (2 * orthogonalOrliczLineConstant γ) * logarithmicFourierEnergy γ ν := by
    rw [lintegral_shifted_angular_eq_circle (f := fun w : UnitCircle ↦ ∫⁻ t : ℝ,
      orliczQuadraticENN γ (orthogonalProjectionDensity ν w t)) (by
        unfold orliczQuadraticENN orliczQuadratic
        fun_prop)]
    exact lintegral_orliczQuadratic_orthogonalProjectionDensity_le γ hγ ν hνenergy
  have hshift : Measurable (fun p : ℝ × ℝ ↦ (p.1 - Real.pi / 2, p.2)) := by fun_prop
  have hline' := Measurable.comp (measurable_angularLineDensity hf) hshift
  have hline : Measurable (fun p : ℝ × ℝ ↦
      orthogonalLineDensity (angularCartesianFrame (p.1 - Real.pi / 2)) f p.2) := by
    simpa only [Function.comp_def] using hline'
  have hQA : Measurable (fun θ ↦ ∫⁻ t : ℝ, orliczQuadraticExtended γ
      (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)) :=
    Measurable.lintegral_prod_right (ν := (volume : Measure ℝ))
      (f := fun θ t : ℝ ↦ orliczQuadraticExtended γ
        (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t))
      ((measurable_orliczQuadraticExtended γ).comp hline)
  calc
    _ ≤ ∫⁻ θ, ((∫⁻ t : ℝ, orliczQuadraticExtended γ
          (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)) +
        ∫⁻ t : ℝ, orliczQuadraticENN γ
          (orthogonalProjectionDensity ν (unitCircleOfAngle (θ - Real.pi / 2)) t))
        ∂radialAngularMeasure := lintegral_mono_ae ha
    _ = (∫⁻ θ, ∫⁻ t : ℝ, orliczQuadraticExtended γ
          (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
          ∂volume ∂radialAngularMeasure) +
        (∫⁻ θ, ∫⁻ t : ℝ, orliczQuadraticENN γ
          (orthogonalProjectionDensity ν (unitCircleOfAngle (θ - Real.pi / 2)) t)
          ∂volume ∂radialAngularMeasure) := lintegral_add_left hQA _
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add hQf hQν

end FalconerThetaGauge
