module

public import FalconerThetaGauge.OrthogonalityKernelFubini

/-! # True two-pair kernel decay from one genuinely cancelling angular factor -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

theorem integral_norm_orthogonalityRadialAmplitude_le {T K v : ℕ} (hT : 1 ≤ T)
    (hK : 6 * T ≤ K) :
    (∫ r : ℝ, ‖orthogonalityRadialAmplitude K v r‖) ≤ 64 * (4 : ℝ) ^ v := by
  let S := tsupport (orthogonalityRadialAmplitude K v)
  have heq : (∫ r : ℝ, ‖orthogonalityRadialAmplitude K v r‖) =
      ∫ r in S, ‖orthogonalityRadialAmplitude K v r‖ := by
    rw [← setIntegral_univ]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
    intro r hr
    simp only [image_eq_zero_of_notMem_tsupport hr.2, norm_zero]
  have hf : ∀ r ∈ S, ‖‖orthogonalityRadialAmplitude K v r‖‖ ≤ 16 * (2 : ℝ) ^ v := by
    intro r hr
    simpa only [iteratedDeriv_zero, pow_zero, mul_one, norm_norm] using
      norm_iteratedDeriv_orthogonalityRadialAmplitude_le_on_support hT hK (j := 0)
        (by omega) hr
  have hS : volume S < ⊤ := by
    have hc := hasCompactSupport_orthogonalityRadialAmplitude K v
    exact hc.isCompact.measure_lt_top
  have hh := norm_setIntegral_le_of_norm_le_const hS hf
  have habs : (∫ r in S, ‖orthogonalityRadialAmplitude K v r‖) ≤
      (16 * (2 : ℝ) ^ v) * volume.real S :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)
  rw [heq]
  calc
    _ ≤ (16 * (2 : ℝ) ^ v) * volume.real S := habs
    _ ≤ (16 * (2 : ℝ) ^ v) * (4 * (2 : ℝ) ^ v) :=
      mul_le_mul_of_nonneg_left (volume_tsupport_orthogonalityRadialAmplitude_le K v)
        (by positivity)
    _ = _ := by
      have hp : ((2 : ℝ) ^ v) ^ 2 = (4 : ℝ) ^ v := by
        rw [← pow_mul, Nat.mul_comm v 2, pow_mul]
        norm_num
      nlinarith [hp]

theorem norm_orthogonalityTwoPairKernel_le_of_angular_cancel {T K v : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) {ℓ q : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1)
    (hq : 0 ≤ q) (arc₁ arc₂ : Fin (angularPartitionCount ℓ))
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (x x' y y' : Plane)
    (hcancel : ∀ r ∈ tsupport (orthogonalityRadialAmplitude K v),
      ‖∫ w, orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w ∂circleArcLength‖ ≤ 2 * ℓ * q) :
    ‖orthogonalityTwoPairKernel K v ℓ arc₁ arc₂ b₁ b₂ x x' y y'‖ ≤
      64 * (4 : ℝ) ^ v * (2 * ℓ) ^ 2 * q := by
  have hi := integrable_orthogonalityTwoPair_outer K v hℓ arc₁ arc₂ hb₁ hb₂
    hbound₁ hbound₂ x x' y y'
  have hh : Integrable (orthogonalityRadialAmplitude K v) :=
    (contDiff_orthogonalityRadialAmplitude K v).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_orthogonalityRadialAmplitude K v)
  have hm : ∀ r, ‖orthogonalityRadialAmplitude K v r *
      (∫ w, orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w ∂circleArcLength) *
      (∫ w, orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w ∂circleArcLength)‖ ≤
        ‖orthogonalityRadialAmplitude K v r‖ * ((2 * ℓ) ^ 2 * q) := by
    intro r
    by_cases hr : r ∈ tsupport (orthogonalityRadialAmplitude K v)
    · simp only [norm_mul]
      calc
        _ ≤ (‖orthogonalityRadialAmplitude K v r‖ * (2 * ℓ * q)) * (2 * ℓ) := by
          gcongr
          · exact hcancel r hr
          · exact norm_integral_orthogonalityCircleKernel_le K hℓ hℓ₁ arc₂ hb₂ hbound₂ y y' r
        _ = _ := by ring
    · simp only [image_eq_zero_of_notMem_tsupport hr, zero_mul, norm_zero, le_refl]
  calc
    _ ≤ ∫ r : ℝ, ‖orthogonalityRadialAmplitude K v r *
        (∫ w, orthogonalityCircleKernel K ℓ arc₁ b₁ x x' r w ∂circleArcLength) *
        (∫ w, orthogonalityCircleKernel K ℓ arc₂ b₂ y y' r w ∂circleArcLength)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r : ℝ, ‖orthogonalityRadialAmplitude K v r‖ * ((2 * ℓ) ^ 2 * q) :=
      integral_mono hi.norm (hh.norm.mul_const _) hm
    _ = (∫ r : ℝ, ‖orthogonalityRadialAmplitude K v r‖) * ((2 * ℓ) ^ 2 * q) :=
      integral_mul_const _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (integral_norm_orthogonalityRadialAmplitude_le hT hK
        (v := v)) (by positivity : 0 ≤ (2 * ℓ) ^ 2 * q)
      simpa only [mul_assoc] using h

end FalconerThetaGauge
