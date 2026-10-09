module

public import FalconerThetaGauge.SpaceSplittingCircle
public import FalconerThetaGauge.OrthogonalityKernelAngularBound

/-! # Genuine frequency measurability and integrability of the circular pair kernels -/

@[expose] public section

noncomputable section

open MeasureTheory Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

theorem stronglyMeasurable_spaceSplittingCircleIntegral
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b)) (x x' : Plane) :
    StronglyMeasurable (fun r : ℝ ↦ spaceSplittingCircleIntegral b r x x') := by
  have hx : Measurable (fun q : ℝ × UnitCircle ↦ b x q.2) :=
    hb.comp (measurable_const.prodMk measurable_snd)
  have hx' : Measurable (fun q : ℝ × UnitCircle ↦ b x' q.2) :=
    hb.comp (measurable_const.prodMk measurable_snd)
  have hm : Measurable (fun q : ℝ × UnitCircle ↦ maskedFourierPairKernel b b q.1 q.2
      (x, x')) := by
    unfold maskedFourierPairKernel
    exact ((by fun_prop : Measurable (fun q : ℝ × UnitCircle ↦ Complex.exp
      (-((q.1 * inner ℝ (x - x') (q.2 : Plane) : ℝ) : ℂ) * Complex.I))).mul
        hx.complex_ofReal).mul hx'.complex_ofReal
  exact hm.stronglyMeasurable.integral_prod_right'

theorem integrable_spaceSplittingCircleIntegral_radial_pair (K v : ℕ)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (x x' y y' : Plane) :
    Integrable (fun r : ℝ ↦ orthogonalityRadialAmplitude K v r *
      spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y') := by
  have hA : Integrable (orthogonalityRadialAmplitude K v) :=
    (contDiff_orthogonalityRadialAmplitude K v).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_orthogonalityRadialAmplitude K v)
  apply (hA.norm.mul_const ((2 * Real.pi) ^ 2)).mono
  · exact (((contDiff_orthogonalityRadialAmplitude K v).continuous.stronglyMeasurable).mul
      (stronglyMeasurable_spaceSplittingCircleIntegral hb₁ x x')).mul
      (stronglyMeasurable_spaceSplittingCircleIntegral hb₂ y y') |>.aestronglyMeasurable
  · filter_upwards [] with r
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg
      (by positivity : 0 ≤ (2 * Real.pi) ^ 2)]
    calc
      _ ≤ ‖orthogonalityRadialAmplitude K v r‖ * (2 * Real.pi) * (2 * Real.pi) :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x') (norm_nonneg _))
          (norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y')
          (norm_nonneg _) (by positivity)
      _ = _ := by ring

end FalconerThetaGauge
