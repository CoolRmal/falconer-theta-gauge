/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierBilinearCauchySchwarz

/-! # Genuine spatial Fourier factorization and angular Fubini -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

def maskedFourierPairKernel (b₁ b₂ : Plane → UnitCircle → ℝ) (r : ℝ)
    (w : UnitCircle) (p : Plane × Plane) : ℂ :=
  Complex.exp (-((r * inner ℝ (p.1 - p.2) (w : Plane) : ℝ) : ℂ) * Complex.I) *
    (b₁ p.1 w : ℂ) * (b₂ p.2 w : ℂ)

theorem spatialFourierPhase_factorization (r : ℝ) (w : UnitCircle) (x y : Plane) :
    Complex.exp (-((r * inner ℝ (x - y) (w : Plane) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) *
        star (Complex.exp (-((r * inner ℝ y (w : Plane) : ℝ) : ℂ) * Complex.I)) := by
  have hc : star (Complex.exp (-((r * inner ℝ y (w : Plane) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((r * inner ℝ y (w : Plane) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  rw [hc, ← Complex.exp_add, inner_sub_left]
  congr 1
  push_cast
  ring

theorem maskedFourierPairKernel_factorization (b₁ b₂ : Plane → UnitCircle → ℝ)
    (r : ℝ) (w : UnitCircle) (p : Plane × Plane) :
    maskedFourierPairKernel b₁ b₂ r w p =
      (Complex.exp (-((r * inner ℝ p.1 (w : Plane) : ℝ) : ℂ) * Complex.I) *
        (b₁ p.1 w : ℂ)) *
      star (Complex.exp (-((r * inner ℝ p.2 (w : Plane) : ℝ) : ℂ) * Complex.I) *
        (b₂ p.2 w : ℂ)) := by
  rw [maskedFourierPairKernel, spatialFourierPhase_factorization, star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

theorem integral_maskedFourierPairKernel (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (r : ℝ) (w : UnitCircle) :
    (∫ p, maskedFourierPairKernel b₁ b₂ r w p ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)) =
      maskedFourierAmplitude ρ₁ X b₁ r w * star (maskedFourierAmplitude ρ₂ Y b₂ r w) := by
  simp_rw [maskedFourierPairKernel_factorization]
  rw [integral_prod_mul
    (fun x ↦ Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) *
      (b₁ x w : ℂ))
    (fun y ↦ star (Complex.exp (-((r * inner ℝ y (w : Plane) : ℝ) : ℂ) * Complex.I) *
      (b₂ y w : ℂ)))]
  simp only [Complex.star_def, integral_conj, maskedFourierAmplitude]

@[fun_prop]
theorem measurable_maskedFourierPairKernel {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) (r : ℝ) :
    Measurable (uncurry (maskedFourierPairKernel b₁ b₂ r)) := by
  have harg₁ : Measurable (fun p : UnitCircle × (Plane × Plane) ↦ (p.2.1, p.1)) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have harg₂ : Measurable (fun p : UnitCircle × (Plane × Plane) ↦ (p.2.2, p.1)) :=
    (measurable_snd.comp measurable_snd).prodMk measurable_fst
  exact ((by fun_prop : Measurable (fun p : UnitCircle × (Plane × Plane) ↦
    Complex.exp (-((r * inner ℝ (p.2.1 - p.2.2) (p.1 : Plane) : ℝ) : ℂ) *
      Complex.I))).mul (hb₁.comp harg₁).complex_ofReal).mul (hb₂.comp harg₂).complex_ofReal

theorem norm_maskedFourierPairKernel (b₁ b₂ : Plane → UnitCircle → ℝ)
    (r : ℝ) (w : UnitCircle) (p : Plane × Plane) :
    ‖maskedFourierPairKernel b₁ b₂ r w p‖ = |b₁ p.1 w| * |b₂ p.2 w| := by
  rw [maskedFourierPairKernel, norm_mul, norm_mul, Complex.norm_exp]
  simp

theorem integral_spatial_circle_maskedFourierPairKernel (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (r : ℝ) :
    (∫ p, ∫ w, (ψ w : ℂ) * maskedFourierPairKernel b₁ b₂ r w p ∂circleArcLength
      ∂(ρ₁.restrict X).prod (ρ₂.restrict Y)) =
      ∫ w, (ψ w : ℂ) * maskedFourierAmplitude ρ₁ X b₁ r w *
        star (maskedFourierAmplitude ρ₂ Y b₂ r w) ∂circleArcLength := by
  have hF : Integrable (fun p : UnitCircle × (Plane × Plane) ↦
      (ψ p.1 : ℂ) * maskedFourierPairKernel b₁ b₂ r p.1 p.2)
      (circleArcLength.prod ((ρ₁.restrict X).prod (ρ₂.restrict Y))) := by
    apply (integrable_const (1 : ℝ)).mono
    · exact (((hψ.comp measurable_fst).complex_ofReal).mul
        (measurable_maskedFourierPairKernel hb₁ hb₂ r)).aestronglyMeasurable
    · filter_upwards [] with p
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_maskedFourierPairKernel,
        norm_one]
      calc
        _ ≤ 1 * (1 * 1) := mul_le_mul (hψ₁ _)
          (mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (abs_nonneg _) (by norm_num))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
        _ = 1 := by ring
  rw [← integral_integral_swap hF]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [integral_const_mul, integral_maskedFourierPairKernel]
  ring

end FalconerThetaGauge
