/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedFourierEnergyAverage
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Actual circular bilinear Fourier amplitudes and their Cauchy--Schwarz bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal

namespace FalconerThetaGauge

theorem norm_integral_bounded_mul_conj_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {ψ : α → ℝ} (hψ : Measurable ψ) (hψ₁ : ∀ x, |ψ x| ≤ 1) :
    ‖∫ x, (ψ x : ℂ) * f x * star (g x) ∂μ‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ) * (∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ) := by
  have hi : Integrable (fun x ↦ ‖f x‖ * ‖g x‖) μ :=
    hf.norm.integrable_mul hg.norm
  have hnorm : ∀ x, ‖(ψ x : ℂ) * f x * star (g x)‖ ≤ ‖f x‖ * ‖g x‖ := by
    intro x
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 1 * ‖f x‖ * ‖g x‖ := by gcongr; exact hψ₁ x
      _ = _ := by ring
  have htwo : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hholder := integral_mul_norm_le_Lp_mul_Lq htwo
    (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hholder
  have hb : ‖∫ x, (ψ x : ℂ) * f x * star (g x) ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ) *
        Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ) := by
    calc
      _ ≤ ∫ x, ‖(ψ x : ℂ) * f x * star (g x)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
        apply integral_mono _ hi hnorm
        apply hi.mono
        · exact ((hψ.complex_ofReal.aestronglyMeasurable.mul hf.aestronglyMeasurable).mul
            hg.aestronglyMeasurable.star).norm
        · filter_upwards [] with x
          simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
            abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hnorm x
      _ ≤ _ := hholder
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow, Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))] using hsq

def maskedFourierBilinearAmplitude (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (ψ : UnitCircle → ℝ) (r : ℝ) : ℂ :=
  (Real.sqrt r : ℂ) * ∫ w, (ψ w : ℂ) * maskedFourierAmplitude ρ₁ X b₁ r w *
    star (maskedFourierAmplitude ρ₂ Y b₂ r w) ∂circleArcLength

theorem maskedFourierAmplitude_memLp_two (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) :
    MemLp (maskedFourierAmplitude ρ X b r) 2 circleArcLength :=
  MemLp.of_bound
    ((measurable_maskedFourierAmplitude ρ X hb).of_uncurry_left.aestronglyMeasurable)
    (ρ.real X) (Eventually.of_forall (norm_maskedFourierAmplitude_le_mass ρ X hb hb₁ r))

theorem norm_maskedFourierBilinearAmplitude_sq_le_integrals (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y b₁ b₂ ψ r‖ ^ 2 ≤
      r * ((∫ w, ‖maskedFourierAmplitude ρ₁ X b₁ r w‖ ^ (2 : ℕ) ∂circleArcLength) *
        (∫ w, ‖maskedFourierAmplitude ρ₂ Y b₂ r w‖ ^ (2 : ℕ) ∂circleArcLength)) := by
  rw [maskedFourierBilinearAmplitude, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hr]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_bounded_mul_conj_sq_le
      (maskedFourierAmplitude_memLp_two ρ₁ X hb₁ hbound₁ r)
      (maskedFourierAmplitude_memLp_two ρ₂ Y hb₂ hbound₂ r) hψ hψ₁) hr

theorem measureReal_mul_maskedCircularSpectrum (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) :
    ρ.real X * maskedCircularSpectrum ρ X b r =
      r * ∫ w, ‖maskedFourierAmplitude ρ X b r w‖ ^ (2 : ℕ) ∂circleArcLength := by
  by_cases hX : ρ.real X = 0
  · have hzero : ∀ w, maskedFourierAmplitude ρ X b r w = 0 := by
      intro w
      exact norm_eq_zero.mp (le_antisymm
        (by simpa only [hX] using norm_maskedFourierAmplitude_le_mass ρ X hb hb₁ r w)
        (norm_nonneg _))
    simp [hX, hzero]
  · unfold maskedCircularSpectrum
    field_simp

/-- The literal Cauchy--Schwarz estimate in Step 3 of Estimate 7.5, including zero-mass cells. -/
theorem norm_maskedFourierBilinearAmplitude_sq_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) {r : ℝ} (hr : 0 < r) :
    ‖maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y b₁ b₂ ψ r‖ ^ 2 ≤
      (ρ₁.real X * ρ₂.real Y) *
        (maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r) / r := by
  have heq : (ρ₁.real X * ρ₂.real Y) *
      (maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r) / r =
      r * ((∫ w, ‖maskedFourierAmplitude ρ₁ X b₁ r w‖ ^ (2 : ℕ) ∂circleArcLength) *
        (∫ w, ‖maskedFourierAmplitude ρ₂ Y b₂ r w‖ ^ (2 : ℕ) ∂circleArcLength)) := by
    calc
      _ = ((ρ₁.real X * maskedCircularSpectrum ρ₁ X b₁ r) *
          (ρ₂.real Y * maskedCircularSpectrum ρ₂ Y b₂ r)) / r := by ring
      _ = _ := by
        rw [measureReal_mul_maskedCircularSpectrum ρ₁ X hb₁ hbound₁,
          measureReal_mul_maskedCircularSpectrum ρ₂ Y hb₂ hbound₂]
        field_simp
  rw [heq]
  exact norm_maskedFourierBilinearAmplitude_sq_le_integrals
    ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁ hr.le

@[fun_prop]
theorem measurable_maskedFourierBilinearAmplitude (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) {ψ : UnitCircle → ℝ} (hψ : Measurable ψ) :
    Measurable (maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y b₁ b₂ ψ) := by
  have hi : Measurable (fun p : ℝ × UnitCircle ↦ (ψ p.2 : ℂ) *
      maskedFourierAmplitude ρ₁ X b₁ p.1 p.2 *
        star (maskedFourierAmplitude ρ₂ Y b₂ p.1 p.2)) :=
    (((hψ.comp measurable_snd).complex_ofReal).mul
      (measurable_maskedFourierAmplitude ρ₁ X hb₁)).mul
      (Complex.continuous_conj.measurable.comp
        (measurable_maskedFourierAmplitude ρ₂ Y hb₂))
  exact Real.continuous_sqrt.measurable.complex_ofReal.mul
    hi.stronglyMeasurable.integral_prod_right'.measurable

end FalconerThetaGauge
