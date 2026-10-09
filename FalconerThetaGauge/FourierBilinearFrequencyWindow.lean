/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierBilinearCauchySchwarz

/-! # The actual frequency-shell integral versus the smooth dyadic average -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter

namespace FalconerThetaGauge

def bilinearFrequencyWindow (v : ℕ) : Set ℝ :=
  Icc ((2 : ℝ) ^ v / 2) (2 * (2 : ℝ) ^ v)

theorem bilinearFrequencyWindow_subset_positive (v : ℕ) :
    bilinearFrequencyWindow v ⊆ Ioi 0 := by
  intro r hr
  exact lt_of_lt_of_le (by positivity) hr.1

theorem maskedFrequencyCutoff_eq_one_on_bilinearFrequencyWindow (K v : ℕ)
    {r : ℝ} (hr : r ∈ bilinearFrequencyWindow v) :
    maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) = 1 := by
  apply maskedFrequencyCutoff_eq_one
  constructor
  · exact (le_div_iff₀ (by positivity)).mpr (by linarith [hr.1])
  · exact (div_le_iff₀ (by positivity)).mpr hr.2

theorem integrableOn_div_bilinearFrequencyWindow (K v : ℕ) {f : ℝ → ℝ}
    (hcut : Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r)) :
    IntegrableOn (fun r ↦ f r / r) (bilinearFrequencyWindow v) := by
  have hf : IntegrableOn f (bilinearFrequencyWindow v) := by
    apply hcut.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [maskedFrequencyCutoff_eq_one_on_bilinearFrequencyWindow K v hr, one_mul]
  have hb : ∀ᵐ r ∂volume.restrict (bilinearFrequencyWindow v),
      ‖r⁻¹‖ ≤ 2 / (2 : ℝ) ^ v := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hrpos := bilinearFrequencyWindow_subset_positive v hr
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hrpos]
    have h := one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) ^ v / 2) hr.1
    simpa only [one_div, inv_div, inv_pow, inv_inv] using h
  simpa only [IntegrableOn, div_eq_mul_inv] using hf.mul_bdd
    measurable_inv.aestronglyMeasurable hb

/-- The literal shell estimate used at the end of Step 3 in Estimate 7.5. -/
theorem integral_bilinearFrequencyWindow_div_le_dyadicAverage (K v : ℕ) {f : ℝ → ℝ}
    (hf : ∀ r ∈ Ioi 0, 0 ≤ f r)
    (hcut : Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r)) :
    (∫ r in bilinearFrequencyWindow v, f r / r) ≤ 2 * dyadicFrequencyAverage K v f := by
  have hpoint : ∀ r ∈ bilinearFrequencyWindow v,
      f r / r ≤ 2 / (2 : ℝ) ^ v *
        (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r) := by
    intro r hr
    have hrpos := bilinearFrequencyWindow_subset_positive v hr
    rw [maskedFrequencyCutoff_eq_one_on_bilinearFrequencyWindow K v hr, one_mul]
    have h := one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) ^ v / 2) hr.1
    have hinv : r⁻¹ ≤ 2 / (2 : ℝ) ^ v := by
      simpa only [one_div, inv_div, inv_pow, inv_inv] using h
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (hf r hrpos)
  calc
    _ ≤ ∫ r in bilinearFrequencyWindow v, 2 / (2 : ℝ) ^ v *
        (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r) :=
      setIntegral_mono_on (integrableOn_div_bilinearFrequencyWindow K v hcut)
        (hcut.const_mul _).integrableOn measurableSet_Icc hpoint
    _ = 2 / (2 : ℝ) ^ v * ∫ r in bilinearFrequencyWindow v,
        maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r := integral_const_mul _ _
    _ ≤ 2 / (2 : ℝ) ^ v * ∫ r in Ioi 0,
        maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply setIntegral_mono_set hcut.integrableOn
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact mul_nonneg (maskedFrequencyCutoff_mem_Icc K _).1 (hf r hr)
      · exact Eventually.of_forall (bilinearFrequencyWindow_subset_positive v)
    _ = _ := by unfold dyadicFrequencyAverage; ring

theorem integral_maskedCircularSpectrum_product_div_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    (∫ r in bilinearFrequencyWindow v,
      maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r / r) ≤
        2 * maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v :=
  integral_bilinearFrequencyWindow_div_le_dyadicAverage K v
    (fun _r hr ↦ mul_nonneg (maskedCircularSpectrum_nonneg ρ₁ X b₁ hr.le)
      (maskedCircularSpectrum_nonneg ρ₂ Y b₂ hr.le))
    (integrable_maskedFourierEnergy_integrand ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v)

theorem integrableOn_maskedFourierBilinearAmplitude_sq (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (K v : ℕ) :
    IntegrableOn (fun r ↦ ‖maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y b₁ b₂ ψ r‖ ^ 2)
      (bilinearFrequencyWindow v) := by
  have hi := integrableOn_div_bilinearFrequencyWindow K v
    (integrable_maskedFourierEnergy_integrand ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v)
  apply (hi.const_mul (ρ₁.real X * ρ₂.real Y)).mono
  · exact ((measurable_maskedFourierBilinearAmplitude
      ρ₁ ρ₂ X Y hb₁ hb₂ hψ).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hrpos := bilinearFrequencyWindow_subset_positive v hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by positivity) (div_nonneg
        (mul_nonneg (maskedCircularSpectrum_nonneg ρ₁ X b₁ hrpos.le)
          (maskedCircularSpectrum_nonneg ρ₂ Y b₂ hrpos.le)) hrpos.le))]
    simpa only [mul_div_assoc] using norm_maskedFourierBilinearAmplitude_sq_le
      ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁ hrpos

/-- Actual integrated bilinear Fourier energy versus the actual dyadic average. -/
theorem integral_maskedFourierBilinearAmplitude_sq_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (K v : ℕ) :
    (∫ r in bilinearFrequencyWindow v,
      ‖maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y b₁ b₂ ψ r‖ ^ 2) ≤
        2 * (ρ₁.real X * ρ₂.real Y) * maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v := by
  have hi := integrableOn_div_bilinearFrequencyWindow K v
    (integrable_maskedFourierEnergy_integrand ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v)
  calc
    _ ≤ ∫ r in bilinearFrequencyWindow v, (ρ₁.real X * ρ₂.real Y) *
        (maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r / r) := by
      apply setIntegral_mono_on
        (integrableOn_maskedFourierBilinearAmplitude_sq ρ₁ ρ₂ X Y
          hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁ K v) (hi.const_mul _)
          measurableSet_Icc
      intro r hr
      simpa only [mul_div_assoc] using norm_maskedFourierBilinearAmplitude_sq_le
        ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁
        (bilinearFrequencyWindow_subset_positive v hr)
    _ = (ρ₁.real X * ρ₂.real Y) * ∫ r in bilinearFrequencyWindow v,
        maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r / r :=
      integral_const_mul _ _
    _ ≤ (ρ₁.real X * ρ₂.real Y) *
        (2 * maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v) :=
      mul_le_mul_of_nonneg_left
        (integral_maskedCircularSpectrum_product_div_le
          ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v) (by positivity)
    _ = _ := by ring

end FalconerThetaGauge
