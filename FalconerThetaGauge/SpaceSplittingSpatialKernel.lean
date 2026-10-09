/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingCircle
public import FalconerThetaGauge.SpaceSplittingNearSchur
public import FalconerThetaGauge.OrthogonalityKernelCrossBound

/-! # The literal four-point averaged circular kernel for space splitting -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

/-- The actual averaged product of the two masked circular integrals. -/
def spaceSplittingAveragedCircleKernel (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ)
    (x x' y y' : Plane) : ℂ :=
  (((2 : ℝ) ^ v : ℝ) : ℂ)⁻¹ * ∫ r in Ioi 0,
    ((maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ 2 : ℝ) : ℂ) *
      spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y'

theorem spaceSplittingAveragedCircleKernel_eq_radial (b₁ b₂ : Plane → UnitCircle → ℝ)
    (K v : ℕ) (x x' y y' : Plane) :
    spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' =
      ∫ r, spaceSplittingCircleIntegral b₁ r x x' *
        spaceSplittingCircleIntegral b₂ r y y' ∂maskedFourierRadialMeasure K v := by
  rw [spaceSplittingAveragedCircleKernel, ← integral_const_mul,
    integral_maskedFourierRadialMeasure]
  simp only [Complex.real_smul, maskedFourierRadialWeight, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_assoc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hzero := maskedFourierRadialWeight_eq_zero_of_nonpos K v (le_of_not_gt hr)
  have he := congrArg Complex.ofReal hzero
  simp only [maskedFourierRadialWeight, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_zero] at he
  simp only [← mul_assoc, he, zero_mul]

@[fun_prop]
theorem measurable_maskedFourierPairKernel_joint {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) :
    Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦
      maskedFourierPairKernel b₁ b₂ q.2.1 q.2.2 q.1) := by
  have h₁ : Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦ b₁ q.1.1 q.2.2) :=
    hb₁.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  have h₂ : Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦ b₂ q.1.2 q.2.2) :=
    hb₂.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  simp only [maskedFourierPairKernel]
  exact ((by fun_prop : Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦
    Complex.exp (-((q.2.1 * inner ℝ (q.1.1 - q.1.2) (q.2.2 : Plane) : ℝ) : ℂ) *
      Complex.I))).mul h₁.complex_ofReal).mul h₂.complex_ofReal

@[fun_prop]
theorem measurable_spaceSplittingCircleIntegral_joint {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) :
    Measurable (fun q : (Plane × Plane) × ℝ ↦
      spaceSplittingCircleIntegral b q.2 q.1.1 q.1.2) := by
  have hm : Measurable (fun q : ((Plane × Plane) × ℝ) × UnitCircle ↦
      maskedFourierPairKernel b b q.1.2 q.2 q.1.1) :=
    (measurable_maskedFourierPairKernel_joint hb hb).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

@[fun_prop]
theorem measurable_spaceSplittingAveragedCircleKernel {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) (K v : ℕ) :
    Measurable (fun p : (Plane × Plane) × (Plane × Plane) ↦
      spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2) := by
  simp_rw [spaceSplittingAveragedCircleKernel_eq_radial]
  have h₁ : Measurable (fun q : ((Plane × Plane) × (Plane × Plane)) × ℝ ↦
      spaceSplittingCircleIntegral b₁ q.2 q.1.1.1 q.1.1.2) :=
    (measurable_spaceSplittingCircleIntegral_joint hb₁).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h₂ : Measurable (fun q : ((Plane × Plane) × (Plane × Plane)) × ℝ ↦
      spaceSplittingCircleIntegral b₂ q.2 q.1.2.1 q.1.2.2) :=
    (measurable_spaceSplittingCircleIntegral_joint hb₂).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact (h₁.mul h₂).stronglyMeasurable.integral_prod_right'.measurable

theorem norm_spaceSplittingAveragedCircleKernel_le {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) (x x' y y' : Plane) :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
      (2 * Real.pi) ^ 2 * (maskedFourierRadialMeasure K v).real univ := by
  rw [spaceSplittingAveragedCircleKernel_eq_radial]
  have h := norm_integral_le_of_norm_le_const (μ := maskedFourierRadialMeasure K v)
    (Filter.Eventually.of_forall (fun r ↦ show
      ‖spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y'‖ ≤
        (2 * Real.pi) ^ 2 by
      rw [norm_mul, pow_two]
      exact mul_le_mul (norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x')
        (norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y')
        (norm_nonneg _) (by positivity)))
  simpa only [mul_comm] using h

theorem integrable_spaceSplittingAveragedCircleKernel
    (μ : Measure ((Plane × Plane) × (Plane × Plane))) [IsFiniteMeasure μ]
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    Integrable (fun p ↦ spaceSplittingAveragedCircleKernel b₁ b₂ K v
      p.1.1 p.1.2 p.2.1 p.2.2) μ := by
  apply (integrable_const ((2 * Real.pi) ^ 2 *
    (maskedFourierRadialMeasure K v).real univ : ℝ)).mono
  · exact (measurable_spaceSplittingAveragedCircleKernel hb₁ hb₂ K v).aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_spaceSplittingAveragedCircleKernel_le hb₁ hb₂ hbound₁ hbound₂ K v
      p.1.1 p.1.2 p.2.1 p.2.2

end FalconerThetaGauge
