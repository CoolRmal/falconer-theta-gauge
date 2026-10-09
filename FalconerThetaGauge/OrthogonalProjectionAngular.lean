module

public import FalconerThetaGauge.OrthogonalProjection
public import FalconerThetaGauge.RadialProjectionOrlicz

/-!
# Angular shifts of the actual orthogonal density bound

The radial-to-line transfer uses the perpendicular angle. The following exact
periodic change of variables keeps the same arc-length average and identifies
the explicit line density with the true orthogonal pushforward density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

theorem angularDirection_add_two_pi (θ : ℝ) :
    angularDirection (θ + 2 * Real.pi) = angularDirection θ := by
  simp [angularDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem lintegral_Ioc_sub_pi_div_two_eq {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hp : ∀ θ, f (θ + 2 * Real.pi) = f θ) :
    (∫⁻ θ in Ioc (-Real.pi) Real.pi, f (θ - Real.pi / 2)) =
      ∫⁻ θ in Ioc (-Real.pi) Real.pi, f θ := by
  have hshift : (∫⁻ θ in Ioc (-Real.pi) Real.pi, f (θ - Real.pi / 2)) =
      ∫⁻ θ in Ioc (-3 * Real.pi / 2) (Real.pi / 2), f θ := by
    have hmp := measurePreserving_add_right (volume : Measure ℝ) (-Real.pi / 2)
    have h := hmp.setLIntegral_comp_preimage
      (s := Ioc (-3 * Real.pi / 2) (Real.pi / 2)) measurableSet_Ioc hf
    have hs : (fun θ : ℝ ↦ θ + (-Real.pi / 2)) ⁻¹'
        Ioc (-3 * Real.pi / 2) (Real.pi / 2) = Ioc (-Real.pi) Real.pi := by
      ext θ
      simp only [mem_preimage, mem_Ioc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hs] at h
    simpa only [← sub_eq_add_neg, neg_div] using h
  have hperiod : (∫⁻ θ in Ioc (-3 * Real.pi / 2) (-Real.pi), f θ) =
      ∫⁻ θ in Ioc (Real.pi / 2) Real.pi, f θ := by
    have hmp := measurePreserving_add_right (volume : Measure ℝ) (2 * Real.pi)
    have h := hmp.setLIntegral_comp_preimage
      (s := Ioc (Real.pi / 2) Real.pi) measurableSet_Ioc hf
    have hs : (fun θ : ℝ ↦ θ + 2 * Real.pi) ⁻¹' Ioc (Real.pi / 2) Real.pi =
        Ioc (-3 * Real.pi / 2) (-Real.pi) := by
      ext θ
      simp only [mem_preimage, mem_Ioc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    simpa only [hs, hp] using h
  have hunion₁ : Ioc (-3 * Real.pi / 2) (-Real.pi) ∪ Ioc (-Real.pi) (Real.pi / 2) =
      Ioc (-3 * Real.pi / 2) (Real.pi / 2) := by
    ext θ
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2, Real.pi_pos]
    · intro h
      by_cases hθ : θ ≤ -Real.pi
      · exact Or.inl ⟨h.1, hθ⟩
      · exact Or.inr ⟨lt_of_not_ge hθ, h.2⟩
  have hunion₂ : Ioc (-Real.pi) (Real.pi / 2) ∪ Ioc (Real.pi / 2) Real.pi =
      Ioc (-Real.pi) Real.pi := by
    ext θ
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2, Real.pi_pos]
    · intro h
      by_cases hθ : θ ≤ Real.pi / 2
      · exact Or.inl ⟨h.1, hθ⟩
      · exact Or.inr ⟨lt_of_not_ge hθ, h.2⟩
  have hdis₁ : Disjoint (Ioc (-3 * Real.pi / 2) (-Real.pi))
      (Ioc (-Real.pi) (Real.pi / 2)) := by
    rw [disjoint_left]
    intro θ h₁ h₂
    exact (not_lt_of_ge h₁.2) h₂.1
  have hdis₂ : Disjoint (Ioc (-Real.pi) (Real.pi / 2))
      (Ioc (Real.pi / 2) Real.pi) := by
    rw [disjoint_left]
    intro θ h₁ h₂
    exact (not_lt_of_ge h₁.2) h₂.1
  rw [hshift, ← hunion₁, lintegral_union measurableSet_Ioc hdis₁, hperiod,
    ← hunion₂, lintegral_union measurableSet_Ioc hdis₂, add_comm]

theorem lintegral_shifted_angular_eq_circle {f : UnitCircle → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ θ, f (unitCircleOfAngle (θ - Real.pi / 2)) ∂radialAngularMeasure) =
      ∫⁻ w, f w ∂circleArcLength := by
  rw [circleArcLength, lintegral_map hf continuous_unitCircleOfAngle.measurable,
    radialAngularMeasure]
  apply lintegral_Ioc_sub_pi_div_two_eq (f := fun θ ↦ f (unitCircleOfAngle θ)) (by fun_prop)
  intro θ
  congr 1
  apply Subtype.ext
  exact angularDirection_add_two_pi θ

theorem orthogonalProjectionDensity_of_withDensity_ae_eq
    {f : Plane → ℝ≥0∞} (hf : Measurable f)
    [IsProbabilityMeasure (volume.withDensity f)] (θ : ℝ) :
    (fun t : ℝ ↦ ENNReal.ofReal
      (orthogonalProjectionDensity (volume.withDensity f) (unitCircleOfAngle θ) t)) =ᵐ[volume]
        orthogonalLineDensity (angularCartesianFrame θ) f := by
  have hd : orthogonalProjectionMeasure (volume.withDensity f) (angularDirection θ) =
      volume.withDensity (orthogonalLineDensity (angularCartesianFrame θ) f) := by
    change (volume.withDensity f).map (fun x ↦ ⟪x, angularDirection θ⟫) = _
    simpa only [angularCartesianFrame_one] using
      map_orthogonal_withDensity_eq (angularCartesianFrame θ) hf
  have hac : orthogonalProjectionKernel (volume.withDensity f) (unitCircleOfAngle θ) ≪ volume := by
    rw [orthogonalProjectionKernel_apply, coe_unitCircleOfAngle, hd]
    exact withDensity_absolutelyContinuous volume _
  have hn := kernelDensity_ae_eq_rnDeriv (orthogonalProjectionKernel (volume.withDensity f))
    volume (a := unitCircleOfAngle θ) hac
  have hr := Measure.rnDeriv_withDensity volume
    (measurable_orthogonalLineDensity (angularCartesianFrame θ) hf)
  have hfin := Measure.rnDeriv_ne_top
    (orthogonalProjectionMeasure (volume.withDensity f) (angularDirection θ)) volume
  rw [← hd] at hr
  filter_upwards [hn, hr, hfin] with t ht hrt hft
  dsimp only [orthogonalProjectionDensity]
  rw [ht, orthogonalProjectionKernel_apply, coe_unitCircleOfAngle,
    ENNReal.ofReal_toReal hft, hrt]

/-- The averaged quadratic Orlicz bound in the exact perpendicular-frame form used
by the radial projection transfer, including the extended value at infinity. -/
theorem lintegral_orliczQuadratic_angularLineDensity_le
    {f : Plane → ℝ≥0∞} (hf : Measurable f)
    [IsProbabilityMeasure (volume.withDensity f)] (γ : ℝ) (hγ : 1 ≤ γ)
    (henergy : logarithmicFourierEnergy γ (volume.withDensity f) ≠ ∞) :
    (∫⁻ θ, ∫⁻ t : ℝ,
      orliczQuadraticExtended γ
        (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
      ∂volume ∂radialAngularMeasure) ≤
      ENNReal.ofReal (2 * orthogonalOrliczLineConstant γ) *
        logarithmicFourierEnergy γ (volume.withDensity f) := by
  calc
    _ = ∫⁻ θ, ∫⁻ t : ℝ, orliczQuadraticENN γ
        (orthogonalProjectionDensity (volume.withDensity f)
          (unitCircleOfAngle (θ - Real.pi / 2)) t) ∂volume ∂radialAngularMeasure := by
      apply lintegral_congr
      intro θ
      apply lintegral_congr_ae
      filter_upwards [orthogonalProjectionDensity_of_withDensity_ae_eq hf
        (θ - Real.pi / 2)] with t ht
      rw [← ht, orliczQuadraticExtended_ofReal]
      exact ENNReal.toReal_nonneg
    _ = ∫⁻ w : UnitCircle, ∫⁻ t : ℝ, orliczQuadraticENN γ
        (orthogonalProjectionDensity (volume.withDensity f) w t)
        ∂volume ∂circleArcLength := by
      apply lintegral_shifted_angular_eq_circle (f := fun w : UnitCircle ↦
        ∫⁻ t : ℝ, orliczQuadraticENN γ (orthogonalProjectionDensity (volume.withDensity f) w t))
      unfold orliczQuadraticENN orliczQuadratic
      fun_prop
    _ ≤ _ := lintegral_orliczQuadratic_orthogonalProjectionDensity_le γ hγ _ henergy

end FalconerThetaGauge
