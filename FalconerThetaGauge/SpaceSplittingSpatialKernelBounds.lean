/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingSpatialKernelFubini

/-! # Actual absolute-integral bounds for the four-point space-splitting kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

theorem spaceSplittingAveragedCircleKernel_eq_full_line
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) (x x' y y' : Plane) :
    spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' =
      ∫ r, orthogonalityRadialAmplitude K v r * spaceSplittingCircleIntegral b₁ r x x' *
        spaceSplittingCircleIntegral b₂ r y y' := by
  rw [spaceSplittingAveragedCircleKernel_eq_radial, integral_maskedFourierRadialMeasure]
  simp only [Complex.real_smul, ← orthogonalityRadialAmplitude_eq_real_weight, mul_assoc]

theorem maskedFourierRadialMeasure_real_univ_le {K : ℕ} (hK : 6 ≤ K) (v : ℕ) :
    (maskedFourierRadialMeasure K v).real univ ≤ 64 * (4 : ℝ) ^ v := by
  have he : (maskedFourierRadialMeasure K v).real univ =
      ∫ r : ℝ, ‖orthogonalityRadialAmplitude K v r‖ := by
    calc
      _ = ∫ _ : ℝ, (1 : ℝ) ∂maskedFourierRadialMeasure K v := by
        simp only [integral_const, smul_eq_mul, mul_one]
      _ = ∫ r : ℝ, maskedFourierRadialWeight K v r := by
        rw [integral_maskedFourierRadialMeasure]
        simp only [smul_eq_mul, mul_one]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with r
        rw [orthogonalityRadialAmplitude_eq_real_weight, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (maskedFourierRadialWeight_nonneg K v r)]
  rw [he]
  exact integral_norm_orthogonalityRadialAmplitude_le (T := 1) (by omega) (by omega)

theorem norm_spaceSplittingAveragedCircleKernel_le_source
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {K : ℕ} (hK : 6 ≤ K) (v : ℕ)
    (x x' y y' : Plane) :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
      64 * (4 : ℝ) ^ v * (2 * Real.pi) ^ 2 := by
  exact (norm_spaceSplittingAveragedCircleKernel_le hb₁ hb₂ hbound₁ hbound₂ K v
    x x' y y').trans (by
      nlinarith [maskedFourierRadialMeasure_real_univ_le hK v,
        sq_nonneg (2 * Real.pi)])

theorem abs_integral_spaceSplittingJointAmplitude_inner_le_integral_norm
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (X X' Y Y' : Set Plane) (K v : ℕ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    |∫ z, inner ℝ (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z)
      (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z)
      ∂maskedFourierJointMeasure K v| ≤
      ∫ p : (Plane × Plane) × (Plane × Plane),
        ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2‖
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y')) := by
  rw [integral_spaceSplittingJointAmplitude_inner_eq_spatial ρ₁ ρ₂ X X' Y Y' K v
    hb₁ hb₂ hbound₁ hbound₂]
  exact (Complex.abs_re_le_norm _).trans (norm_integral_le_integral_norm _)

theorem abs_integral_spaceSplittingJointAmplitude_inner_le_lintegral_norm
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (X X' Y Y' : Set Plane) (K v : ℕ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    |∫ z, inner ℝ (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z)
      (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z)
      ∂maskedFourierJointMeasure K v| ≤
      (∫⁻ p : (Plane × Plane) × (Plane × Plane), ENNReal.ofReal
        ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2‖
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y'))).toReal := by
  rw [integral_spaceSplittingJointAmplitude_inner_eq_spatial ρ₁ ρ₂ X X' Y Y' K v
    hb₁ hb₂ hbound₁ hbound₂]
  exact (Complex.abs_re_le_norm _).trans (norm_integral_le_lintegral_norm _)

end FalconerThetaGauge
