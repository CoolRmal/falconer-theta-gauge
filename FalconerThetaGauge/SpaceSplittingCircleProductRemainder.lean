module

public import FalconerThetaGauge.SpaceSplittingSpatialKernelBounds
public import FalconerThetaGauge.SpaceSplittingCircleRemainder
public import FalconerThetaGauge.ScheduledSymbolEnergy

/-! # The true averaged product of the circular stationary remainders is negligible -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

theorem ae_maskedFourierRadialMeasure_window (K v : ℕ) :
    ∀ᵐ r ∂maskedFourierRadialMeasure K v,
      (2 : ℝ) ^ v / 4 ≤ r ∧ r ≤ 4 * (2 : ℝ) ^ v := by
  rw [maskedFourierRadialMeasure, ae_withDensity_iff
    (measurable_maskedFourierRadialWeight K v).ennreal_ofReal]
  filter_upwards [] with r hr
  have hs : 0 < (2 : ℝ) ^ v := by positivity
  have hc : maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) ≠ 0 := by
    intro hc
    apply hr
    simp only [maskedFourierRadialWeight, hc, mul_zero, zero_mul, ENNReal.ofReal_zero]
  have hm : r / (2 : ℝ) ^ v ∈ Icc (1 / 4) 4 := by
    by_contra hm
    exact hc (maskedFrequencyCutoff_eq_zero K hm)
  exact ⟨by have := (le_div_iff₀ hs).1 hm.1; linarith,
    (div_le_iff₀ hs).1 hm.2⟩

@[fun_prop]
theorem measurable_spaceSplittingStationaryMain (T : ℕ) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) : Measurable (fun r ↦ spaceSplittingStationaryMain T b r x x') := by
  unfold spaceSplittingStationaryMain
  fun_prop

theorem norm_circle_product_sub_stationary_product_le {Ix Iy Mx My : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hx : ‖Ix‖ ≤ 2 * Real.pi) (hy : ‖Iy‖ ≤ 2 * Real.pi)
    (hex : ‖Ix - Mx‖ ≤ δ) (hey : ‖Iy - My‖ ≤ δ) :
    ‖Ix * Iy - Mx * My‖ ≤ (4 * Real.pi + δ) * δ := by
  have hMx : ‖Mx‖ ≤ 2 * Real.pi + δ := by
    have h' := norm_add_le (Mx - Ix) Ix
    rw [sub_add_cancel, norm_sub_rev] at h'
    linarith
  have heq : Ix * Iy - Mx * My = (Ix - Mx) * Iy + Mx * (Iy - My) := by ring
  rw [heq]
  calc
    _ ≤ ‖Ix - Mx‖ * ‖Iy‖ + ‖Mx‖ * ‖Iy - My‖ := by
      simpa only [norm_mul] using norm_add_le ((Ix - Mx) * Iy) (Mx * (Iy - My))
    _ ≤ δ * (2 * Real.pi) + (2 * Real.pi + δ) * δ :=
      add_le_add (mul_le_mul hex hy (norm_nonneg _) hδ)
        (mul_le_mul hMx hey (norm_nonneg _) (by positivity))
    _ = _ := by ring

set_option maxHeartbeats 800000 in
theorem norm_averaged_circle_product_sub_stationary_product_le
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (Function.uncurry b₁))
    (hb₂ : Measurable (Function.uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v T : ℕ) (x x' y y' : Plane) {δ : ℝ} (hδ : 0 ≤ δ)
    (hex : ∀ᵐ r ∂maskedFourierRadialMeasure K v,
      ‖spaceSplittingCircleIntegral b₁ r x x' -
        spaceSplittingStationaryMain T b₁ r x x'‖ ≤ δ)
    (hey : ∀ᵐ r ∂maskedFourierRadialMeasure K v,
      ‖spaceSplittingCircleIntegral b₂ r y y' -
        spaceSplittingStationaryMain T b₂ r y y'‖ ≤ δ) :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' -
      ∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        spaceSplittingStationaryMain T b₁ r x x' *
          spaceSplittingStationaryMain T b₂ r y y'‖ ≤
      (maskedFourierRadialMeasure K v).real univ * (4 * Real.pi + δ) * δ := by
  let μ := maskedFourierRadialMeasure K v
  have hm₁ := measurable_spaceSplittingStationaryMain T b₁ x x'
  have hm₂ := measurable_spaceSplittingStationaryMain T b₂ y y'
  have hc₁ : Measurable (fun r ↦ spaceSplittingCircleIntegral b₁ r x x') :=
    Measurable.of_uncurry_left
      (f := fun (q : Plane × Plane) (r : ℝ) ↦ spaceSplittingCircleIntegral b₁ r q.1 q.2)
      (x := (x, x')) (measurable_spaceSplittingCircleIntegral_joint hb₁)
  have hc₂ : Measurable (fun r ↦ spaceSplittingCircleIntegral b₂ r y y') :=
    Measurable.of_uncurry_left
      (f := fun (q : Plane × Plane) (r : ℝ) ↦ spaceSplittingCircleIntegral b₂ r q.1 q.2)
      (x := (y, y')) (measurable_spaceSplittingCircleIntegral_joint hb₂)
  have hiC : Integrable (fun r ↦ spaceSplittingCircleIntegral b₁ r x x' *
      spaceSplittingCircleIntegral b₂ r y y') μ := by
    apply (integrable_const ((2 * Real.pi) ^ 2 : ℝ)).mono (hc₁.mul hc₂).aestronglyMeasurable
    filter_upwards [] with r
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul (norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x')
      (norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y') (norm_nonneg _) (by positivity)
  have hiM : Integrable (fun r ↦ spaceSplittingStationaryMain T b₁ r x x' *
      spaceSplittingStationaryMain T b₂ r y y') μ := by
    apply (integrable_const ((2 * Real.pi + δ) ^ 2 : ℝ)).mono
      (hm₁.mul hm₂).aestronglyMeasurable
    filter_upwards [hex, hey] with r hex hey
    have h₁ := norm_add_le (spaceSplittingStationaryMain T b₁ r x x' -
      spaceSplittingCircleIntegral b₁ r x x') (spaceSplittingCircleIntegral b₁ r x x')
    have h₂ := norm_add_le (spaceSplittingStationaryMain T b₂ r y y' -
      spaceSplittingCircleIntegral b₂ r y y') (spaceSplittingCircleIntegral b₂ r y y')
    rw [sub_add_cancel, norm_sub_rev] at h₁ h₂
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul (by linarith [norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x'])
      (by linarith [norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y'])
      (norm_nonneg _) (by positivity)
  have heq : (∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        spaceSplittingStationaryMain T b₁ r x x' *
          spaceSplittingStationaryMain T b₂ r y y') =
      ∫ r, spaceSplittingStationaryMain T b₁ r x x' *
        spaceSplittingStationaryMain T b₂ r y y' ∂μ := by
    rw [integral_maskedFourierRadialMeasure]
    simp only [Complex.real_smul, ← orthogonalityRadialAmplitude_eq_real_weight, mul_assoc]
  rw [spaceSplittingAveragedCircleKernel_eq_radial, heq, ← integral_sub hiC hiM]
  have hb : ∀ᵐ r ∂μ, ‖spaceSplittingCircleIntegral b₁ r x x' *
      spaceSplittingCircleIntegral b₂ r y y' -
      spaceSplittingStationaryMain T b₁ r x x' *
        spaceSplittingStationaryMain T b₂ r y y'‖ ≤ (4 * Real.pi + δ) * δ := by
    filter_upwards [hex, hey] with r hex hey
    exact norm_circle_product_sub_stationary_product_le hδ
      (norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x')
      (norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y') hex hey
  simpa only [μ, mul_assoc, mul_comm, mul_left_comm] using
    (norm_integral_le_of_norm_le_const hb)

end FalconerThetaGauge
