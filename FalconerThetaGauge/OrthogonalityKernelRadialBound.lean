module

public import FalconerThetaGauge.OrthogonalityKernelAngularBound

/-! # Cancellation of the actual two-circle kernel when the radial phase separates -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

def orthogonalityRadialPhase (x x' y y' : Plane) (w₁ w₂ : UnitCircle) : ℝ :=
  inner ℝ (x - x') (w₁ : Plane) + inner ℝ (y - y') (w₂ : Plane)

theorem orthogonalityCircleKernel_zero (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) (w : UnitCircle) :
    orthogonalityCircleKernel K ℓ arc b x x' 0 w =
      orthogonalityCircleAmplitude K ℓ arc b x x' w := by
  simp only [orthogonalityCircleKernel, zero_mul, Complex.ofReal_zero, neg_zero,
    Complex.exp_zero, one_mul]

theorem orthogonality_radial_integrand_factorization (K v : ℕ) (ℓ : ℝ)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x x' y y' : Plane) (r : ℝ) (w₁ w₂ : UnitCircle) :
    orthogonalityRadialAmplitude K v r *
      (orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w₁ *
        orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w₂) =
      (orthogonalityCircleAmplitude K ℓ arc₁ b₁ x x' w₁ *
        orthogonalityCircleAmplitude K ℓ arc₂ b₂ y y' w₂) *
      (Complex.exp (-((r * orthogonalityRadialPhase x x' y y' w₁ w₂ : ℝ) : ℂ) *
        Complex.I) * orthogonalityRadialAmplitude K v r) := by
  have he : Complex.exp (-((r * inner ℝ (x - x') (w₁ : Plane) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((r * inner ℝ (y - y') (w₂ : Plane) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((r * orthogonalityRadialPhase x x' y y' w₁ w₂ : ℝ) : ℂ) *
        Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [orthogonalityRadialPhase, Complex.ofReal_mul, Complex.ofReal_add]
    ring
  simp only [orthogonalityCircleKernel]
  linear_combination orthogonalityRadialAmplitude K v r *
    orthogonalityCircleAmplitude K ℓ arc₁ b₁ x x' w₁ *
    orthogonalityCircleAmplitude K ℓ arc₂ b₂ y y' w₂ * he

theorem norm_orthogonalityTwoPairKernel_le_of_radial_cancel (K v : ℕ) {ℓ q : ℝ}
    (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (hq : 0 ≤ q)
    (arc₁ arc₂ : Fin (angularPartitionCount ℓ)) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane)
    (hcancel : ∀ w₁ w₂, equalArcCutoff K ℓ arc₁ w₁ ≠ 0 →
      equalArcCutoff K ℓ arc₂ w₂ ≠ 0 →
      ‖∫ r : ℝ, Complex.exp (-((r * orthogonalityRadialPhase x x' y y' w₁ w₂ : ℝ) : ℂ) *
        Complex.I) * orthogonalityRadialAmplitude K v r‖ ≤ q) :
    ‖orthogonalityTwoPairKernel K v ℓ arc₁ arc₂ b₁ b₂ x x' y y'‖ ≤ (2 * ℓ) ^ 2 * q := by
  let A₁ := orthogonalityCircleAmplitude K ℓ arc₁ b₁ x x'
  let A₂ := orthogonalityCircleAmplitude K ℓ arc₂ b₂ y y'
  have hA₁ : Integrable (fun w ↦ ‖A₁ w‖) circleArcLength := by
    simpa only [A₁, orthogonalityCircleKernel_zero] using
      (integrable_orthogonalityCircleKernel K hℓ arc₁ hb₁ hbound₁ x x' 0).norm
  have hA₂ : Integrable (fun w ↦ ‖A₂ w‖) circleArcLength := by
    simpa only [A₂, orthogonalityCircleKernel_zero] using
      (integrable_orthogonalityCircleKernel K hℓ arc₂ hb₂ hbound₂ y y' 0).norm
  have hi := integrable_orthogonalityTwoPair_integrand K v hℓ arc₁ arc₂ hb₁ hb₂
    hbound₁ hbound₂ x x' y y'
  have hp : ∀ w : UnitCircle × UnitCircle,
      ‖∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        (orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w.1 *
          orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w.2)‖ ≤ ‖A₁ w.1‖ * ‖A₂ w.2‖ * q := by
    intro w
    simp_rw [orthogonality_radial_integrand_factorization]
    rw [integral_const_mul, norm_mul, norm_mul]
    by_cases h₁ : equalArcCutoff K ℓ arc₁ w.1 = 0
    · simp only [A₁, orthogonalityCircleAmplitude, h₁, Complex.ofReal_zero, zero_mul,
        norm_zero, le_refl]
    by_cases h₂ : equalArcCutoff K ℓ arc₂ w.2 = 0
    · simp only [A₂, orthogonalityCircleAmplitude, h₂, Complex.ofReal_zero, zero_mul,
        norm_zero, mul_zero, le_refl]
    exact mul_le_mul_of_nonneg_left (hcancel _ _ h₁ h₂) (by positivity)
  rw [orthogonalityTwoPairKernel_eq_radial_first K v hℓ arc₁ arc₂ hb₁ hb₂ hbound₁ hbound₂]
  calc
    _ ≤ ∫ w : UnitCircle × UnitCircle, ‖∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        (orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w.1 *
          orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w.2)‖
        ∂circleArcLength.prod circleArcLength :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w : UnitCircle × UnitCircle, ‖A₁ w.1‖ * ‖A₂ w.2‖ * q
        ∂circleArcLength.prod circleArcLength :=
      integral_mono hi.integral_prod_right.norm ((hA₁.mul_prod hA₂).mul_const q) hp
    _ = ((∫ w, ‖A₁ w‖ ∂circleArcLength) * (∫ w, ‖A₂ w‖ ∂circleArcLength)) * q := by
      rw [integral_mul_const,
        integral_prod_mul (fun w : UnitCircle ↦ ‖A₁ w‖) (fun w : UnitCircle ↦ ‖A₂ w‖)]
    _ ≤ _ := by
      have h₁ : (∫ w, ‖A₁ w‖ ∂circleArcLength) ≤ 2 * ℓ := by
        simpa only [A₁, orthogonalityCircleKernel_zero] using
          integral_norm_orthogonalityCircleKernel_le K hℓ hℓ₁ arc₁ hb₁ hbound₁ x x' 0
      have h₂ : (∫ w, ‖A₂ w‖ ∂circleArcLength) ≤ 2 * ℓ := by
        simpa only [A₂, orthogonalityCircleKernel_zero] using
          integral_norm_orthogonalityCircleKernel_le K hℓ hℓ₁ arc₂ hb₂ hbound₂ y y' 0
      simpa only [pow_two] using mul_le_mul_of_nonneg_right
        (mul_le_mul h₁ h₂ (integral_nonneg fun _ ↦ norm_nonneg _) (by positivity)) hq

end FalconerThetaGauge
