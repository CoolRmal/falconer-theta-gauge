module

public import FalconerThetaGauge.OrthogonalityCircleBounds

/-! # Genuine radial-circle Fubini for the actual compact dyadic kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

theorem integrable_radial_mul_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {h : ℝ → ℂ} (hh : Integrable h)
    {f : ℝ × α → ℂ} (hf : Measurable f) (hbound : ∀ p, ‖f p‖ ≤ 1) :
    Integrable (fun p : ℝ × α ↦ h p.1 * f p) (volume.prod μ) := by
  apply (hh.norm.comp_fst μ).mono
  · exact (hh.aestronglyMeasurable.comp_fst.mul hf.aestronglyMeasurable)
  · filter_upwards [] with p
    rw [norm_mul, Real.norm_eq_abs, abs_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) (hbound p)

theorem integrable_orthogonalityCircleKernel (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hbound : ∀ x w, |b x w| ≤ 1)
    (x x' : Plane) (r : ℝ) :
    Integrable (orthogonalityCircleKernel K ℓ arc b x x' r) circleArcLength := by
  apply (integrable_const (1 : ℝ)).mono
  · have hm : Measurable (orthogonalityCircleKernel K ℓ arc b x x' r) :=
      (measurable_orthogonalityCircleKernel K hℓ arc hb x x').of_uncurry_left
    exact hm.aestronglyMeasurable
  · filter_upwards [] with w
    simpa only [norm_one] using norm_orthogonalityCircleKernel_le_one K hℓ arc hbound x x' r w

def orthogonalityTwoPairKernel (K v : ℕ) (ℓ : ℝ)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x x' y y' : Plane) : ℂ :=
  ∫ r : ℝ, orthogonalityRadialAmplitude K v r *
    (∫ w, orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w ∂circleArcLength) *
    (∫ w, orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w ∂circleArcLength)

theorem integrable_orthogonalityTwoPair_integrand (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) :
    Integrable (fun p : ℝ × (UnitCircle × UnitCircle) ↦
      orthogonalityRadialAmplitude K v p.1 *
        (orthogonalityCircleKernel K ℓ arc₁ b₁ x x' p.1 p.2.1 *
          orthogonalityCircleKernel K ℓ arc₂ b₂ y y' p.1 p.2.2))
      (volume.prod (circleArcLength.prod circleArcLength)) := by
  apply integrable_radial_mul_bounded (circleArcLength.prod circleArcLength)
    ((contDiff_orthogonalityRadialAmplitude K v).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_orthogonalityRadialAmplitude K v))
  · have hm₁ : Measurable (fun p : ℝ × (UnitCircle × UnitCircle) ↦
        orthogonalityCircleKernel K ℓ arc₁ b₁ x x' p.1 p.2.1) :=
      (measurable_orthogonalityCircleKernel K hℓ arc₁ hb₁ x x').comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hm₂ : Measurable (fun p : ℝ × (UnitCircle × UnitCircle) ↦
        orthogonalityCircleKernel K ℓ arc₂ b₂ y y' p.1 p.2.2) :=
      (measurable_orthogonalityCircleKernel K hℓ arc₂ hb₂ y y').comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact hm₁.mul hm₂
  · intro p
    rw [norm_mul]
    exact (mul_le_mul (norm_orthogonalityCircleKernel_le_one K hℓ arc₁ hbound₁ x x' _ _)
      (norm_orthogonalityCircleKernel_le_one K hℓ arc₂ hbound₂ y y' _ _)
      (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem orthogonalityTwoPairKernel_eq_radial_first (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) :
    orthogonalityTwoPairKernel K v ℓ arc₁ arc₂ b₁ b₂ x x' y y' =
      ∫ w : UnitCircle × UnitCircle, ∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        (orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w.1 *
          orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w.2) ∂volume
        ∂circleArcLength.prod circleArcLength := by
  have hi := integrable_orthogonalityTwoPair_integrand K v hℓ arc₁ arc₂ hb₁ hb₂
    hbound₁ hbound₂ x x' y y'
  rw [← integral_integral_swap hi]
  unfold orthogonalityTwoPairKernel
  apply integral_congr_ae
  filter_upwards [] with r
  rw [integral_const_mul, integral_prod_mul]
  ring

theorem integrable_orthogonalityTwoPair_outer (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) :
    Integrable (fun r : ℝ ↦ orthogonalityRadialAmplitude K v r *
      (∫ w, orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w ∂circleArcLength) *
      (∫ w, orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w ∂circleArcLength)) := by
  apply (integrable_orthogonalityTwoPair_integrand K v hℓ arc₁ arc₂ hb₁ hb₂
    hbound₁ hbound₂ x x' y y').integral_prod_left.congr
  filter_upwards [] with r
  rw [integral_const_mul, integral_prod_mul]
  ring

theorem orthogonalityTwoPairKernel_swap (K v : ℕ) (ℓ : ℝ)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x x' y y' : Plane) :
    orthogonalityTwoPairKernel K v ℓ arc₁ arc₂ b₁ b₂ x x' y y' =
      orthogonalityTwoPairKernel K v ℓ arc₂ arc₁ b₂ b₁ y y' x x' := by
  apply integral_congr_ae
  filter_upwards [] with r
  ring

end FalconerThetaGauge
