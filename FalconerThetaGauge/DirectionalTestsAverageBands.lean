module

public import FalconerThetaGauge.DirectionalTestsAverageAngles

/-! # The genuine planar dot-product arc bands used in the source average counts -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

/-- The Euclidean dot product of actual unit-angle vectors. -/
theorem inner_angularDirection_eq_cos (a b : ℝ) :
    inner ℝ (angularDirection a) (angularDirection b) = Real.cos (b - a) := by
  rw [angularDirection, angularDirection, LinearIsometryEquiv.inner_map_map, Complex.inner]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im, mul_zero, add_zero, zero_add, mul_one]
  rw [Real.cos_sub]
  ring

/-- The true polar-coordinate formula for an arbitrary nonzero planar vector. -/
theorem inner_vector_angularDirection_eq (v : Plane) (hv : v ≠ 0) (θ : ℝ) :
    inner ℝ v (angularDirection θ) = ‖v‖ * Real.cos (θ - radialAngle 0 v) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hrep : ‖v‖ • angularDirection (radialAngle 0 v) = v := by
    rw [angularDirection_radialAngle (Ne.symm hv), sub_zero, smul_smul,
      mul_inv_cancel₀ hn, one_smul]
  conv_lhs => rw [← hrep, real_inner_smul_left, inner_angularDirection_eq_cos]

/-- The literal set of directions satisfying the planar pair dot-product test. -/
def dotDirectionBand (v : Plane) (η : ℝ) : Set UnitCircle :=
  {w | |inner ℝ v (w : Plane)| ≤ η}

theorem measurableSet_dotDirectionBand (v : Plane) (η : ℝ) :
    MeasurableSet (dotDirectionBand v η) := by
  apply (isClosed_le _ continuous_const).measurableSet
  exact (continuous_const.inner continuous_subtype_val).abs

/-- The exact source direction-band bound, with the true planar norm in the denominator. -/
theorem circleArcLength_dotDirectionBand_le (v : Plane) (hv : v ≠ 0) {η : ℝ}
    (hη : 0 ≤ η) :
    circleArcLength (dotDirectionBand v η) ≤
      ENNReal.ofReal (2 * Real.pi * min 1 (η / ‖v‖)) := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have heq : unitCircleOfAngle ⁻¹' dotDirectionBand v η =
      {θ : ℝ | |Real.cos (θ - radialAngle 0 v)| ≤ η / ‖v‖} := by
    ext θ
    simp only [mem_preimage, dotDirectionBand, mem_ofPred_eq, coe_unitCircleOfAngle,
      inner_vector_angularDirection_eq v hv, abs_mul, abs_of_pos hn]
    rw [mul_comm ‖v‖]
    exact (le_div_iff₀ hn).symm
  have hm : Measurable unitCircleOfAngle := by
    exact (continuous_angularDirection.subtype_mk (by intro θ; simp)).measurable
  rw [circleArcLength, Measure.map_apply hm (measurableSet_dotDirectionBand v η),
    radialAngularMeasure, Measure.restrict_apply (hm (measurableSet_dotDirectionBand v η)),
    heq, inter_comm]
  exact volume_shifted_cosine_band_le _ (div_nonneg hη hn.le)

/-- Orthogonal-line distance is exactly the absolute dot product with the
perpendicular unit-angle vector; this is the actual planar residual. -/
theorem directionLineResidual_norm_eq_abs_inner_quarterAngle (c z : Plane) (θ : ℝ) :
    ‖directionLineResidual c (unitCircleOfAngle θ) z‖ =
      |inner ℝ (z - c) (angularDirection (θ + Real.pi / 2))| := by
  by_cases hv : z - c = 0
  · simp only [directionLineResidual, hv, inner_zero_right, zero_smul, sub_zero,
      norm_zero, inner_zero_left, abs_zero]
  have hnorm : ‖directionLineResidual c (unitCircleOfAngle θ) z‖ ^ 2 =
      ‖z - c‖ ^ 2 - (inner ℝ (z - c) (angularDirection θ)) ^ 2 := by
    simp only [directionLineResidual, coe_unitCircleOfAngle]
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
      norm_angularDirection, Real.norm_eq_abs, mul_one, sq_abs,
      real_inner_comm (angularDirection θ) (z - c)]
    ring
  have h₁ := inner_vector_angularDirection_eq (z - c) hv θ
  have h₂ := inner_vector_angularDirection_eq (z - c) hv (θ + Real.pi / 2)
  rw [show θ + Real.pi / 2 - radialAngle 0 (z - c) =
      (θ - radialAngle 0 (z - c)) + Real.pi / 2 by ring, Real.cos_add_pi_div_two] at h₂
  have htrig := Real.sin_sq_add_cos_sq (θ - radialAngle 0 (z - c))
  have hs : ‖directionLineResidual c (unitCircleOfAngle θ) z‖ ^ 2 =
      |inner ℝ (z - c) (angularDirection (θ + Real.pi / 2))| ^ 2 := by
    rw [hnorm, h₁, h₂, sq_abs]
    nlinarith [sq_nonneg ‖z - c‖]
  nlinarith [norm_nonneg (directionLineResidual c (unitCircleOfAngle θ) z),
    abs_nonneg (inner ℝ (z - c) (angularDirection (θ + Real.pi / 2)))]

/-- Literal direction bands for distance to an actual affine line. -/
def lineDistanceDirectionBand (c z : Plane) (η : ℝ) : Set UnitCircle :=
  {w | ‖directionLineResidual c w z‖ ≤ η}

theorem measurableSet_lineDistanceDirectionBand (c z : Plane) (η : ℝ) :
    MeasurableSet (lineDistanceDirectionBand c z η) :=
  (isClosed_le (continuous_directionLineResidual c z).norm continuous_const).measurableSet

/-- The same exact source arc bound controls the true affine-line distance test. -/
theorem circleArcLength_lineDistanceDirectionBand_le (c z : Plane) (hz : z ≠ c) {η : ℝ}
    (hη : 0 ≤ η) :
    circleArcLength (lineDistanceDirectionBand c z η) ≤
      ENNReal.ofReal (2 * Real.pi * min 1 (η / ‖z - c‖)) := by
  have hv : z - c ≠ 0 := sub_ne_zero.mpr hz
  have hn : 0 < ‖z - c‖ := norm_pos_iff.mpr hv
  have heq : unitCircleOfAngle ⁻¹' lineDistanceDirectionBand c z η =
      {θ : ℝ | |Real.cos (θ - (radialAngle 0 (z - c) - Real.pi / 2))| ≤ η / ‖z - c‖} := by
    ext θ
    simp only [mem_preimage, lineDistanceDirectionBand, mem_ofPred_eq,
      directionLineResidual_norm_eq_abs_inner_quarterAngle,
      inner_vector_angularDirection_eq (z - c) hv, abs_mul, abs_of_pos hn]
    rw [show θ + Real.pi / 2 - radialAngle 0 (z - c) =
      θ - (radialAngle 0 (z - c) - Real.pi / 2) by ring, mul_comm ‖z - c‖]
    exact (le_div_iff₀ hn).symm
  rw [circleArcLength, Measure.map_apply continuous_unitCircleOfAngle.measurable
      (measurableSet_lineDistanceDirectionBand c z η), radialAngularMeasure,
    Measure.restrict_apply (continuous_unitCircleOfAngle.measurable
      (measurableSet_lineDistanceDirectionBand c z η)), heq, inter_comm]
  exact volume_shifted_cosine_band_le _ (div_nonneg hη hn.le)

end FalconerThetaGauge
