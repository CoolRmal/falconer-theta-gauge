module

public import FalconerThetaGauge.RadialProjectionRay
public import Mathlib.Analysis.Complex.Isometry

/-!
# Actual orthogonal densities and the radial full-line identity

In an orthonormal Cartesian frame, integrating a planar density along the second
coordinate gives the density of its actual first-coordinate orthogonal pushforward.
The identity holds pointwise along every fiber, so it can be used with singular
pin measures. These arguments adapt `FalconerPacking.RadialProjectionLine`
(original source credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/RadialProjectionLine.lean
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

/-- The genuine line density in an orthonormal Cartesian frame. -/
def orthogonalLineDensity (e : ℂ ≃ₗᵢ[ℝ] Plane) (f : Plane → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, f (e (t + r * Complex.I))

@[fun_prop]
theorem measurable_orthogonalLineDensity (e : ℂ ≃ₗᵢ[ℝ] Plane)
    {f : Plane → ℝ≥0∞} (hf : Measurable f) : Measurable (orthogonalLineDensity e f) := by
  unfold orthogonalLineDensity
  fun_prop

theorem re_symm_eq_inner (e : ℂ ≃ₗᵢ[ℝ] Plane) (x : Plane) : (e.symm x).re = ⟪x, e 1⟫ := by
  rw [← e.symm.inner_map_map x (e 1), LinearIsometryEquiv.symm_apply_apply]
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply, RCLike.re_eq_complex_re]
  simp

/-- The full-line integral is the exact orthogonal density at the projected pin. -/
theorem lineIntegral_eq_orthogonalLineDensity (e : ℂ ≃ₗᵢ[ℝ] Plane)
    (f : Plane → ℝ≥0∞) (x : Plane) :
    (∫⁻ r : ℝ, f (x + r • e Complex.I)) = orthogonalLineDensity e f ⟪x, e 1⟫ := by
  let z := e.symm x
  have heq (r : ℝ) : x + r • e Complex.I =
      e ((z.re : ℂ) + ((z.im + r : ℝ) : ℂ) * Complex.I) := by
    apply e.symm.injective
    simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]
    change z + r • Complex.I = _
    rw [Complex.real_smul]
    apply Complex.ext <;> simp
  simp_rw [heq]
  rw [lintegral_add_left_eq_self (fun r : ℝ ↦ f (e (z.re + r * Complex.I))) z.im]
  rw [orthogonalLineDensity, ← re_symm_eq_inner]

theorem lintegral_orthogonalLineDensity (e : ℂ ≃ₗᵢ[ℝ] Plane)
    {f : Plane → ℝ≥0∞} (hf : Measurable f) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t : ℝ, g t * orthogonalLineDensity e f t) = ∫⁻ x, g ⟪x, e 1⟫ * f x := by
  calc
    (∫⁻ t : ℝ, g t * orthogonalLineDensity e f t) =
        ∫⁻ z : ℝ × ℝ, g z.1 * f (e (z.1 + z.2 * Complex.I)) := by
      rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro t
      simpa only [orthogonalLineDensity] using
        (lintegral_const_mul (g t) (f := fun r : ℝ ↦ f (e (t + r * Complex.I)))
          (by fun_prop)).symm
    _ = ∫⁻ z : ℂ, g z.re * f (e z) := by
      have h := Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb
        Complex.measurableEquivRealProd.symm.measurableEmbedding
        (fun z : ℂ ↦ g z.re * f (e z))
      simpa [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I] using h
    _ = ∫⁻ x, g ⟪x, e 1⟫ * f x := by
      have h := e.measurePreserving.lintegral_comp_emb e.toHomeomorph.measurableEmbedding
        (fun x ↦ g ⟪x, e 1⟫ * f x)
      simpa only [← re_symm_eq_inner, LinearIsometryEquiv.symm_apply_apply] using h

/-- The actual orthogonal projection of a Lebesgue-density source has its explicit line density. -/
theorem map_orthogonal_withDensity_eq (e : ℂ ≃ₗᵢ[ℝ] Plane)
    {f : Plane → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (fun x ↦ ⟪x, e 1⟫) =
      volume.withDensity (orthogonalLineDensity e f) := by
  apply Measure.ext
  intro S hS
  have hproj : Measurable (fun x : Plane ↦ ⟪x, e 1⟫) := by fun_prop
  rw [Measure.map_apply hproj hS, withDensity_apply _ (hproj hS), withDensity_apply _ hS]
  have h := lintegral_orthogonalLineDensity e hf
    (g := S.indicator 1) (measurable_const.indicator hS)
  rw [← lintegral_indicator hS, ← lintegral_indicator (hproj hS)]
  convert h.symm using 1
  · apply lintegral_congr
    intro y
    by_cases hy : ⟪y, e 1⟫ ∈ S <;> simp [hy]
  · apply lintegral_congr
    intro t
    by_cases ht : t ∈ S <;> simp [ht]

/-- The Cartesian frame whose first direction has angle `θ`. -/
def angularCartesianFrame (θ : ℝ) : ℂ ≃ₗᵢ[ℝ] Plane :=
  (rotation (Circle.exp θ)).trans Complex.orthonormalBasisOneI.repr

theorem angularCartesianFrame_apply (θ : ℝ) (z : ℂ) :
    angularCartesianFrame θ z =
      Complex.orthonormalBasisOneI.repr (Complex.exp (θ * Complex.I) * z) := rfl

@[simp]
theorem angularCartesianFrame_one (θ : ℝ) : angularCartesianFrame θ 1 = angularDirection θ := by
  simp only [angularCartesianFrame_apply, mul_one, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, angularDirection]

@[simp]
theorem angularCartesianFrame_I (θ : ℝ) :
    angularCartesianFrame θ Complex.I = angularDirection (θ + Real.pi / 2) := by
  rw [angularCartesianFrame_apply, Complex.exp_mul_I]
  unfold angularDirection
  congr 1
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;> simp [Real.cos_add, Real.sin_add]

@[fun_prop]
theorem measurable_angularLineDensity {f : Plane → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : ℝ × ℝ ↦ orthogonalLineDensity (angularCartesianFrame z.1) f z.2) := by
  unfold orthogonalLineDensity
  simp only [angularCartesianFrame_apply]
  fun_prop

/-- Pointwise radial-to-orthogonal projection comparison, at every pin and angle. -/
theorem circleUnweightedRayDensity_le_orthogonalLineDensity (f : Plane → ℝ≥0∞)
    (x : Plane) (θ : ℝ) :
    circleUnweightedRayDensity f x (unitCircleOfAngle θ) ≤
      orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f
        ⟪x, angularDirection (θ - Real.pi / 2)⟫ := by
  have h := lineIntegral_eq_orthogonalLineDensity
    (angularCartesianFrame (θ - Real.pi / 2)) f x
  simp only [angularCartesianFrame_I, angularCartesianFrame_one, sub_add_cancel] at h
  rw [← h]
  exact circleUnweightedRayDensity_le_lineIntegral f x (unitCircleOfAngle θ)

/-- The full-line integral is pushed to the actual, potentially singular pin projection. -/
theorem lintegral_lineIntegral_comp_eq {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (ν : Measure Plane) (θ : ℝ) {Ψ : ℝ≥0∞ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ x, Ψ (∫⁻ r : ℝ, f (x + r • angularDirection θ)) ∂ν) =
      ∫⁻ t : ℝ, Ψ (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
        ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫) := by
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro x
  congr 1
  have h := lineIntegral_eq_orthogonalLineDensity
    (angularCartesianFrame (θ - Real.pi / 2)) f x
  simpa only [angularCartesianFrame_I, angularCartesianFrame_one, sub_add_cancel] using h

/-- The actual weighted radial densities transfer to orthogonal line densities, retaining the
possibly singular pin measure and any measurable increasing Orlicz integrand. -/
theorem lintegral_circleUnweightedRayDensity_comp_le_orthogonal
    {f : Plane → ℝ≥0∞} (hf : Measurable f) (ν : Measure Plane) [SFinite ν]
    {Ψ : ℝ≥0∞ → ℝ≥0∞} (hΨ : Measurable Ψ) (hΨmono : Monotone Ψ) :
    (∫⁻ x, ∫⁻ w, Ψ (circleUnweightedRayDensity f x w) ∂circleArcLength ∂ν) ≤
      ∫⁻ θ, ∫⁻ t : ℝ,
        Ψ (orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
          ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫)
        ∂radialAngularMeasure := by
  have heq : (∫⁻ x, ∫⁻ w, Ψ (circleUnweightedRayDensity f x w) ∂circleArcLength ∂ν) =
      ∫⁻ θ, ∫⁻ x, Ψ (circleUnweightedRayDensity f x (unitCircleOfAngle θ))
        ∂ν ∂radialAngularMeasure := by
    rw [lintegral_lintegral_swap (by fun_prop), circleArcLength,
      lintegral_map (by fun_prop) continuous_unitCircleOfAngle.measurable]
  rw [heq]
  apply lintegral_mono
  intro θ
  dsimp only
  rw [← lintegral_lineIntegral_comp_eq hf ν θ hΨ]
  apply lintegral_mono
  intro x
  exact hΨmono (circleUnweightedRayDensity_le_lineIntegral f x (unitCircleOfAngle θ))

/-- For a source with bounded pin-to-source distance, its actual radial densities obey the
same transfer with the explicit maximal-distance factor inside the integrand. -/
theorem lintegral_circleRayDensity_comp_le_orthogonal {f : Plane → ℝ≥0∞}
    (hf : Measurable f) (ν : Measure Plane) [SFinite ν] {R : ℝ}
    (hR : ∀ᵐ x ∂ν, ∀ y, f y ≠ 0 → dist x y ≤ R)
    {Ψ : ℝ≥0∞ → ℝ≥0∞} (hΨ : Measurable Ψ) (hΨmono : Monotone Ψ) :
    (∫⁻ x, ∫⁻ w, Ψ (circleRayDensity f x w) ∂circleArcLength ∂ν) ≤
      ∫⁻ θ, ∫⁻ t : ℝ,
        Ψ (ENNReal.ofReal R *
          orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t)
          ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫)
        ∂radialAngularMeasure := by
  have heq : (∫⁻ x, ∫⁻ w, Ψ (circleRayDensity f x w) ∂circleArcLength ∂ν) =
      ∫⁻ θ, ∫⁻ x, Ψ (circleRayDensity f x (unitCircleOfAngle θ)) ∂ν
        ∂radialAngularMeasure := by
    rw [lintegral_lintegral_swap (by fun_prop), circleArcLength,
      lintegral_map (by fun_prop) continuous_unitCircleOfAngle.measurable]
  rw [heq]
  apply lintegral_mono
  intro θ
  have hΨR : Measurable (fun a : ℝ≥0∞ ↦ Ψ (ENNReal.ofReal R * a)) := by fun_prop
  dsimp only
  rw [← lintegral_lineIntegral_comp_eq hf ν θ hΨR]
  apply lintegral_mono_ae
  filter_upwards [hR] with x hx
  exact hΨmono (circleRayDensity_le_lineIntegral hf x hx (unitCircleOfAngle θ))

end FalconerThetaGauge
