module

public import FalconerThetaGauge.MaskedMattilaSymbolInversion
public import FalconerThetaGauge.DirectionalTestsAverageBands

/-! # Literal Euclidean circle kernels for the normalized masked Mattila inversion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff RealInnerProductSpace

namespace FalconerThetaGauge

def preparedInverseCircleAmplitude (T : ℕ) (α : ℝ) (B : ℝ → ℂ)
    (j : ℕ) (w : UnitCircle) : ℂ :=
  (preparedArcCutoff (6 * T) α w : ℂ) * stationaryPhaseInverseOperator j B (circleAngle w)

def preparedInverseCircleKernelIntegral (T : ℕ) (α : ℝ) (B : ℝ → ℂ)
    (z : Plane) (r : ℝ) (j : ℕ) : ℂ :=
  ∫ w, Complex.exp (-((r * inner ℝ z (w : Plane) : ℝ) : ℂ) * Complex.I) *
    preparedInverseCircleAmplitude T α B j w ∂circleArcLength

def preparedInverseCircleKernelSeries (T : ℕ) (α : ℝ) (B : ℝ → ℂ)
    (z : Plane) (r : ℝ) : ℂ :=
  ∑ j ∈ Finset.range T, ((r * ‖z‖ : ℝ) : ℂ)⁻¹ ^ j *
    preparedInverseCircleKernelIntegral T α B z r j

theorem measurable_preparedInverseCircleAmplitude (T : ℕ) (α : ℝ)
    {B : ℝ → ℂ} (hB : ContDiff ℝ ∞ B) (j : ℕ) :
    Measurable (preparedInverseCircleAmplitude T α B j) := by
  exact (measurable_preparedArcCutoff _ _).complex_ofReal.mul
    ((contDiff_stationaryPhaseInverseOperator hB j).continuous.measurable.comp
      measurable_circleAngle)

theorem preparedInverseCircleAmplitude_comp_angle (T : ℕ) (α : ℝ)
    {B : ℝ → ℂ} (hB : Periodic B (2 * Real.pi)) (j : ℕ) (t : ℝ) :
    preparedInverseCircleAmplitude T α B j (unitCircleOfAngle t) =
      preparedAngularAmplitude (6 * T) α (stationaryPhaseInverseOperator j B) t := by
  simp only [preparedInverseCircleAmplitude, circleAngle_unitCircleOfAngle,
    periodic_apply_toIocMod (periodic_stationaryPhaseInverseOperator hB j),
    preparedAngularAmplitude, preparedAngularCutoff, Pi.mul_apply]

/-- Actual circle arc length and the planar dot-product kernel give precisely the
one-turn angular integral used in the proved stationary inversion. -/
theorem preparedInverseCircleKernelIntegral_eq_angular (T : ℕ) (α : ℝ)
    {B : ℝ → ℂ} (hBs : ContDiff ℝ ∞ B) (hBP : Periodic B (2 * Real.pi))
    {z : Plane} (hz : z ≠ 0) (r : ℝ) (j : ℕ) :
    preparedInverseCircleKernelIntegral T α B z r j =
      preparedInverseCircleIntegral T α B (radialAngle 0 z) (r * ‖z‖) (-Real.pi) j := by
  have hm : Measurable (fun w : UnitCircle ↦
      Complex.exp (-((r * inner ℝ z (w : Plane) : ℝ) : ℂ) * Complex.I) *
        preparedInverseCircleAmplitude T α B j w) :=
    (show Measurable (fun w : UnitCircle ↦
      Complex.exp (-((r * inner ℝ z (w : Plane) : ℝ) : ℂ) * Complex.I)) by fun_prop).mul
      (measurable_preparedInverseCircleAmplitude T α hBs j)
  rw [preparedInverseCircleKernelIntegral, circleArcLength,
    integral_map continuous_unitCircleOfAngle.measurable.aemeasurable hm.aestronglyMeasurable]
  rw [radialAngularMeasure, preparedInverseCircleIntegral,
    show -Real.pi + 2 * Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [preparedInverseCircleAmplitude_comp_angle _ _ hBP, coe_unitCircleOfAngle,
    inner_vector_angularDirection_eq z hz t, mul_assoc]

theorem preparedInverseCircleKernelSeries_eq_angular (T : ℕ) (α : ℝ)
    {B : ℝ → ℂ} (hBs : ContDiff ℝ ∞ B) (hBP : Periodic B (2 * Real.pi))
    {z : Plane} (hz : z ≠ 0) (r : ℝ) :
    preparedInverseCircleKernelSeries T α B z r =
      preparedInverseCircleSeries T α B (radialAngle 0 z) (r * ‖z‖) (-Real.pi) := by
  simp only [preparedInverseCircleKernelSeries, preparedInverseCircleSeries,
    preparedInverseCircleKernelIntegral_eq_angular _ _ hBs hBP hz]

theorem pairDirection_eq_unitCircleOfAngle_difference (x y : Plane) :
    pairDirection x y = unitCircleOfAngle (radialAngle 0 (x - y)) := by
  simp only [pairDirection, radialProjection, radialAngle, sub_zero]

end FalconerThetaGauge
