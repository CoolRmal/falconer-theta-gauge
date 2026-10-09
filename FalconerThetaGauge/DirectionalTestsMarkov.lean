module

public import FalconerThetaGauge.FilteredDistanceMeasureCircle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The exact arc-length Markov estimate for the actual directional tests -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- The actual average with respect to unnormalized circle arc length. -/
def directionalAverage (f : UnitCircle → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ w, f w ∂circleArcLength

/-- Strict failure of the source's comparison against the actual angular average. -/
def directionalTestFailure (q : ℝ) (f : UnitCircle → ℝ) : Set UnitCircle :=
  {w | q * directionalAverage f < f w}

theorem measurableSet_directionalTestFailure (q : ℝ) {f : UnitCircle → ℝ}
    (hf : Measurable f) : MeasurableSet (directionalTestFailure q f) :=
  measurableSet_lt measurable_const hf

/-- Markov's inequality gives exactly `2π/q`, including the case of a zero average. -/
theorem circleArcLength_directionalTestFailure_le {q : ℝ} (hq : 0 < q)
    {f : UnitCircle → ℝ} (hf : Integrable f circleArcLength) (hpos : ∀ w, 0 ≤ f w) :
    circleArcLength (directionalTestFailure q f) ≤ ENNReal.ofReal (2 * Real.pi / q) := by
  have hI : 0 ≤ ∫ w, f w ∂circleArcLength := integral_nonneg hpos
  by_cases hzero : (∫ w, f w ∂circleArcLength) = 0
  · have hae := (integral_eq_zero_iff_of_nonneg hpos hf).mp hzero
    have hnull : circleArcLength (directionalTestFailure q f) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae] with w hw
      simp only [directionalTestFailure, mem_ofPred_eq, directionalAverage, hzero,
        mul_zero, hw, Pi.zero_apply, lt_self_iff_false, not_false_eq_true]
    rw [hnull]
    exact bot_le
  · have hIpos : 0 < ∫ w, f w ∂circleArcLength := lt_of_le_of_ne hI (Ne.symm hzero)
    have ht : 0 < q * directionalAverage f := by
      unfold directionalAverage
      positivity
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall hpos) hf (q * directionalAverage f)
    have hmono : circleArcLength.real (directionalTestFailure q f) ≤
        circleArcLength.real {w | q * directionalAverage f ≤ f w} := by
      refine measureReal_mono ?_ (measure_ne_top circleArcLength _)
      intro w hw
      change q * directionalAverage f < f w at hw
      exact hw.le
    have hreal : circleArcLength.real (directionalTestFailure q f) ≤ 2 * Real.pi / q := by
      apply (mul_le_mul_iff_right₀ ht).mp
      calc
        _ ≤ q * directionalAverage f *
            circleArcLength.real {w | q * directionalAverage f ≤ f w} :=
          mul_le_mul_of_nonneg_left hmono ht.le
        _ ≤ ∫ w, f w ∂circleArcLength := hmark
        _ = q * directionalAverage f * (2 * Real.pi / q) := by
          unfold directionalAverage
          field_simp
    have h := ENNReal.ofReal_le_ofReal hreal
    rwa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top circleArcLength _)] at h

theorem directionalTestFailure_antipodal (q : ℝ) {f : UnitCircle → ℝ}
    (hf : ∀ w, f (circleAntipode w) = f w) (w : UnitCircle) :
    circleAntipode w ∈ directionalTestFailure q f ↔ w ∈ directionalTestFailure q f := by
  simp only [directionalTestFailure, mem_ofPred_eq, hf]

end FalconerThetaGauge
