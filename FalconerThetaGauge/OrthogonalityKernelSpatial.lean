module

public import FalconerThetaGauge.OrthogonalityKernelUnlinked

/-! # Actual spatial integration of the unlinked oscillatory kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman

@[fun_prop]
theorem measurable_orthogonalityCircleKernel_joint (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) :
    Measurable (fun p : (Plane × Plane) × (ℝ × UnitCircle) ↦
      orthogonalityCircleKernel K ℓ arc b p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h₁ : Measurable (fun p : (Plane × Plane) × (ℝ × UnitCircle) ↦ b p.1.1 p.2.2) :=
    hb.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  have h₂ : Measurable (fun p : (Plane × Plane) × (ℝ × UnitCircle) ↦ b p.1.2 p.2.2) :=
    hb.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  have hχ : Measurable (fun p : (Plane × Plane) × (ℝ × UnitCircle) ↦
      equalArcCutoff K ℓ arc p.2.2) :=
    (measurable_equalArcCutoff K hℓ arc).comp (measurable_snd.comp measurable_snd)
  simp only [orthogonalityCircleKernel, orthogonalityCircleAmplitude, mul_assoc]
  exact (by fun_prop : Measurable (fun p : (Plane × Plane) × (ℝ × UnitCircle) ↦
      Complex.exp (-((p.2.1 * inner ℝ (p.1.1 - p.1.2) (p.2.2 : Plane) : ℝ) : ℂ) *
        Complex.I))).fun_mul (hχ.complex_ofReal.fun_mul
          (h₁.complex_ofReal.fun_mul h₂.complex_ofReal))

@[fun_prop]
theorem measurable_orthogonalityTwoPairKernel (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) :
    Measurable (fun z : (Plane × Plane) × (Plane × Plane) ↦
      orthogonalityTwoPairKernel K v ℓ arc₁ arc₂ b₁ b₂ z.1.1 z.1.2 z.2.1 z.2.2) := by
  have hm₁ : Measurable (fun p : (((Plane × Plane) × (Plane × Plane)) × ℝ) × UnitCircle ↦
      orthogonalityCircleKernel K ℓ arc₁ b₁ p.1.1.1.1 p.1.1.1.2 p.1.2 p.2) :=
    (measurable_orthogonalityCircleKernel_joint K hℓ arc₁ hb₁).comp
      (((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hm₂ : Measurable (fun p : (((Plane × Plane) × (Plane × Plane)) × ℝ) × UnitCircle ↦
      orthogonalityCircleKernel K ℓ arc₂ b₂ p.1.1.2.1 p.1.1.2.2 p.1.2 p.2) :=
    (measurable_orthogonalityCircleKernel_joint K hℓ arc₂ hb₂).comp
      (((measurable_snd.comp measurable_fst).comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h₁ := (hm₁.stronglyMeasurable.integral_prod_right' (ν := circleArcLength)).measurable
  have h₂ := (hm₂.stronglyMeasurable.integral_prod_right' (ν := circleArcLength)).measurable
  have hrad : Measurable (fun p : ((Plane × Plane) × (Plane × Plane)) × ℝ ↦
      orthogonalityRadialAmplitude K v p.2) :=
    (contDiff_orthogonalityRadialAmplitude K v).continuous.measurable.comp measurable_snd
  exact (((hrad.mul h₁).mul h₂).stronglyMeasurable.integral_prod_right').measurable

theorem norm_orthogonalityTwoPairKernel_le (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓ₁ : ℓ ≤ 1) (hK : 6 ≤ K) (arc₁ arc₂ : Fin (angularPartitionCount ℓ))
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (x x' y y' : Plane) :
    ‖orthogonalityTwoPairKernel K v ℓ arc₁ arc₂ b₁ b₂ x x' y y'‖ ≤
      64 * (4 : ℝ) ^ v * (2 * ℓ) ^ 2 := by
  simpa only [mul_one] using norm_orthogonalityTwoPairKernel_le_of_angular_cancel
    (T := 1) (by norm_num) hK hℓ hℓ₁ (by norm_num) arc₁ arc₂ hb₁ hb₂
    hbound₁ hbound₂ x x' y y' (q := 1) (fun r _ ↦ by
      simpa only [mul_one] using
        norm_integral_orthogonalityCircleKernel_le K hℓ hℓ₁ arc₁ hb₁ hbound₁ x x' r)

end FalconerThetaGauge
