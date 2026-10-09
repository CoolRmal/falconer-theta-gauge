module

public import FalconerThetaGauge.RadialProjectionPolar

/-!
# Actual circle densities from positive rays

For a Lebesgue-density source, the radial pushforward has its explicit positive-ray
density including the polar Jacobian. The inverse-distance weighted source cancels
that Jacobian exactly, producing the one-sided line integral in Theorem 5.4.

The polar testing argument and bounded-Jacobian comparison follow
`FalconerPacking.RadialProjectionRay` (original source credits Yongxi Lin, Apache 2.0),
at commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/RadialProjectionRay.lean
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

@[simp]
theorem norm_unitCircle (w : UnitCircle) : ‖(w : Plane)‖ = 1 := by
  simp

/-- The actual radial projection is constant on each oriented positive ray. -/
theorem radialProjection_ray (x : Plane) (w : UnitCircle) {r : ℝ} (hr : 0 < r) :
    radialProjection x (x + r • (w : Plane)) = w := by
  have hdist : dist (x + r • (w : Plane)) x = r := by
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, norm_unitCircle, mul_one]
  have hne : x ≠ x + r • (w : Plane) := by
    intro heq
    rw [← heq, dist_self] at hdist
    exact hr.ne' hdist.symm
  apply Subtype.ext
  rw [coe_radialProjection_of_ne hne]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    norm_unitCircle, mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The circle density of a radial pushforward, including the radial Jacobian. -/
def circleRayDensity (f : Plane → ℝ≥0∞) (x : Plane) (w : UnitCircle) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * f (x + r • (w : Plane))

@[fun_prop]
theorem measurable_circleRayDensity {f : Plane → ℝ≥0∞} (hf : Measurable f) :
    Measurable (Function.uncurry (circleRayDensity f)) := by
  unfold Function.uncurry circleRayDensity
  fun_prop

/-- Polar coordinates tested against a measurable function of the actual circle direction. -/
theorem lintegral_circleRayDensity {f : Plane → ℝ≥0∞} (hf : Measurable f) (x : Plane)
    {g : UnitCircle → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ w, g w * circleRayDensity f x w ∂circleArcLength) =
      ∫⁻ y, g (radialProjection x y) * f y := by
  let F : Plane → ℝ≥0∞ := fun v ↦ g (radialProjection x (x + v)) * f (x + v)
  have hpolar := lintegral_polar_euclidean F
  have hsource : (∫⁻ v, F v) = ∫⁻ y, g (radialProjection x y) * f y :=
    lintegral_add_left_eq_self (fun y ↦ g (radialProjection x y) * f y) x
  rw [hsource] at hpolar
  calc
    (∫⁻ w, g w * circleRayDensity f x w ∂circleArcLength) =
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal r * (g (unitCircleOfAngle θ) * f (x + r • angularDirection θ)) := by
      rw [circleArcLength, lintegral_map (by fun_prop) continuous_unitCircleOfAngle.measurable,
        radialAngularMeasure, ← setLIntegral_congr Ioo_ae_eq_Ioc]
      apply lintegral_congr
      intro θ
      rw [circleRayDensity, ← lintegral_const_mul (g (unitCircleOfAngle θ)) (by fun_prop)]
      apply lintegral_congr
      intro r
      ac_rfl
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 *
            (g (unitCircleOfAngle p.2) * f (x + p.1 • angularDirection p.2)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      symm
      apply lintegral_prod_symm
      fun_prop
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * F (p.1 • angularDirection p.2) := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      simp only [F, ← coe_unitCircleOfAngle,
        radialProjection_ray x (unitCircleOfAngle p.2) hp.1]
    _ = ∫⁻ y, g (radialProjection x y) * f y := hpolar

/-- The actual circle pushforward has its explicit jointly measurable positive-ray density. -/
theorem map_radialProjection_withDensity_eq {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (x : Plane) :
    (volume.withDensity f).map (radialProjection x) =
      circleArcLength.withDensity (circleRayDensity f x) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_radialProjection.of_uncurry_left hS,
    withDensity_apply _ (measurable_radialProjection.of_uncurry_left hS),
    withDensity_apply _ hS]
  have h := lintegral_circleRayDensity hf x
    (g := S.indicator 1) (measurable_const.indicator hS)
  rw [← lintegral_indicator hS,
    ← lintegral_indicator (measurable_radialProjection.of_uncurry_left hS)]
  convert h.symm using 1
  · apply lintegral_congr
    intro y
    by_cases hy : radialProjection x y ∈ S <;> simp [hy]
  · apply lintegral_congr
    intro w
    by_cases hw : w ∈ S <;> simp [hw]

/-- The one-sided ray integral without a Jacobian, used for the weighted density. -/
def circleUnweightedRayDensity (f : Plane → ℝ≥0∞) (x : Plane) (w : UnitCircle) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), f (x + r • (w : Plane))

@[fun_prop]
theorem measurable_circleUnweightedRayDensity {f : Plane → ℝ≥0∞} (hf : Measurable f) :
    Measurable (Function.uncurry (circleUnweightedRayDensity f)) := by
  unfold Function.uncurry circleUnweightedRayDensity
  fun_prop

/-- Inverse distance cancels the polar Jacobian exactly on every positive ray. -/
theorem circleRayDensity_inverse_distance (f : Plane → ℝ≥0∞) (x : Plane) (w : UnitCircle) :
    circleRayDensity (fun y ↦ (ENNReal.ofReal (dist x y))⁻¹ * f y) x w =
      circleUnweightedRayDensity f x w := by
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hdist : dist x (x + r • (w : Plane)) = r := by
    rw [dist_comm]
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < r from hr), norm_unitCircle, mul_one]
  dsimp only
  rw [hdist, ← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top, one_mul]

/-- The literal inverse-distance weighted source has the unweighted ray integral as its
circle radial density. This is the first projection identity in Theorem 5.4. -/
theorem map_inverse_distance_radialProjection_withDensity_eq {f : Plane → ℝ≥0∞}
    (hf : Measurable f) (x : Plane) :
    (volume.withDensity (fun y ↦ (ENNReal.ofReal (dist x y))⁻¹ * f y)).map
        (radialProjection x) =
      circleArcLength.withDensity (circleUnweightedRayDensity f x) := by
  rw [map_radialProjection_withDensity_eq (by fun_prop)]
  congr 1
  funext w
  exact circleRayDensity_inverse_distance f x w

/-- Removing the positive-ray restriction gives the actual full-line integral. -/
theorem circleUnweightedRayDensity_le_lineIntegral (f : Plane → ℝ≥0∞)
    (x : Plane) (w : UnitCircle) :
    circleUnweightedRayDensity f x w ≤ ∫⁻ r : ℝ, f (x + r • (w : Plane)) :=
  setLIntegral_le_lintegral _ _

/-- A bounded radial Jacobian bounds the actual unweighted source projection density by
the full-line integral, with the source's actual maximal pin-to-source distance. -/
theorem circleRayDensity_le_lineIntegral {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (x : Plane) {R : ℝ} (hR : ∀ y, f y ≠ 0 → dist x y ≤ R) (w : UnitCircle) :
    circleRayDensity f x w ≤ ENNReal.ofReal R * ∫⁻ r : ℝ, f (x + r • (w : Plane)) := by
  calc
    circleRayDensity f x w ≤
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal R * f (x + r • (w : Plane)) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro r hr
      by_cases hz : f (x + r • (w : Plane)) = 0
      · simp [hz]
      have hdist : dist x (x + r • (w : Plane)) = r := by
        rw [dist_comm]
        simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (show 0 < r from hr), norm_unitCircle, mul_one]
      have hrR : r ≤ R := by simpa only [hdist] using hR _ hz
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hrR) le_rfl
    _ = ENNReal.ofReal R * circleUnweightedRayDensity f x w :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal R * ∫⁻ r : ℝ, f (x + r • (w : Plane)) :=
      mul_le_mul' le_rfl (circleUnweightedRayDensity_le_lineIntegral f x w)

end FalconerThetaGauge
