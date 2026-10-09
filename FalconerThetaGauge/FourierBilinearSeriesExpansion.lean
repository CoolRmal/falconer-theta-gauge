/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierBilinearSeriesIntegral
public import FalconerThetaGauge.FourierBilinearFrequencyWindow

/-! # Step 3 for the genuine countable separated Fourier expansion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter

namespace FalconerThetaGauge

theorem norm_maskedFourierBilinearAmplitude_sq_le_on_window (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (v : ℕ) {r : ℝ}
    (hr : r ∈ bilinearFrequencyWindow v) :
    ‖maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y b₁ b₂ ψ r‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 * (2 * (2 : ℝ) ^ v) * (ρ₁.real X * ρ₂.real Y) ^ 2 := by
  have hrpos := bilinearFrequencyWindow_subset_positive v hr
  calc
    _ ≤ (ρ₁.real X * ρ₂.real Y) *
        (maskedCircularSpectrum ρ₁ X b₁ r * maskedCircularSpectrum ρ₂ Y b₂ r) / r :=
      norm_maskedFourierBilinearAmplitude_sq_le
        ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ hψ hψ₁ hrpos
    _ ≤ (ρ₁.real X * ρ₂.real Y) *
        ((2 * Real.pi) ^ 2 * r ^ 2 * (ρ₁.real X * ρ₂.real Y)) / r := by
      apply div_le_div_of_nonneg_right _ hrpos.le
      exact mul_le_mul_of_nonneg_left
        (maskedCircularSpectrum_mul_le ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ hrpos.le)
        (by positivity)
    _ = (2 * Real.pi) ^ 2 * r * (ρ₁.real X * ρ₂.real Y) ^ 2 := by
      field_simp
    _ ≤ _ := by gcongr; exact hr.2

theorem summable_weighted_maskedFourierEnergy {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (has : Summable a) (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : ι → Plane → UnitCircle → ℝ} (hb₁ : ∀ i, Measurable (uncurry (b₁ i)))
    (hb₂ : ∀ i, Measurable (uncurry (b₂ i))) (hbound₁ : ∀ i x w, |b₁ i x w| ≤ 1)
    (hbound₂ : ∀ i x w, |b₂ i x w| ≤ 1) (K v : ℕ) :
    Summable (fun i ↦ a i * maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ i) (b₂ i) K v) := by
  apply (has.mul_right (2600 * (4 : ℝ) ^ v * (ρ₁.real X * ρ₂.real Y))).of_nonneg_of_le
  · exact fun i ↦ mul_nonneg (ha i) (maskedFourierEnergy_nonneg _ _ _ _ _ _ _ _)
  · exact fun i ↦ mul_le_mul_of_nonneg_left
      (maskedFourierEnergy_le ρ₁ ρ₂ X Y (hb₁ i) (hb₂ i) (hbound₁ i) (hbound₂ i) K v)
      (ha i)

/-- The genuine countable version of the integrated Cauchy--Schwarz step in Estimate 7.5. -/
theorem integral_tsum_maskedFourierBilinearAmplitude_sq_le {ι : Type*} [Countable ι]
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : ι → Plane → UnitCircle → ℝ} (hb₁ : ∀ i, Measurable (uncurry (b₁ i)))
    (hb₂ : ∀ i, Measurable (uncurry (b₂ i))) (hbound₁ : ∀ i x w, |b₁ i x w| ≤ 1)
    (hbound₂ : ∀ i x w, |b₂ i x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (K v : ℕ)
    {c : ι → ℝ → ℂ} {a : ι → ℝ} (hc : ∀ i, Measurable (c i))
    (ha : ∀ i, 0 ≤ a i) (has : Summable a)
    (hca : ∀ i, ∀ r ∈ bilinearFrequencyWindow v, ‖c i r‖ ≤ a i) :
    (∫ r in bilinearFrequencyWindow v,
      ‖∑' i, c i r *
        maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y (b₁ i) (b₂ i) ψ r‖ ^ 2) ≤
      2 * (ρ₁.real X * ρ₂.real Y) * (∑' i, a i) *
        ∑' i, a i * maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ i) (b₂ i) K v := by
  let : IsFiniteMeasure (volume.restrict (bilinearFrequencyWindow v)) := by
    unfold bilinearFrequencyWindow
    infer_instance
  let Z : ι → ℝ → ℂ := fun i ↦ maskedFourierBilinearAmplitude
    ρ₁ ρ₂ X Y (b₁ i) (b₂ i) ψ
  have hbase := integral_norm_tsum_mul_sq_le_weighted
    (μ := volume.restrict (bilinearFrequencyWindow v))
    (by positivity : 0 ≤ (2 * Real.pi) ^ 2 * (2 * (2 : ℝ) ^ v) *
      (ρ₁.real X * ρ₂.real Y) ^ 2) hc
    (fun i ↦ measurable_maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y (hb₁ i) (hb₂ i) hψ)
    ha has (fun i ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hca i r hr) (fun i ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact norm_maskedFourierBilinearAmplitude_sq_le_on_window
        ρ₁ ρ₂ X Y (hb₁ i) (hb₂ i) (hbound₁ i) (hbound₂ i) hψ hψ₁ v hr)
  have hsF := summable_weighted_maskedFourierEnergy
    ha has ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K v
  have hweight : ∀ i, a i * (∫ r in bilinearFrequencyWindow v, ‖Z i r‖ ^ 2) ≤
      2 * (ρ₁.real X * ρ₂.real Y) *
        (a i * maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ i) (b₂ i) K v) := by
    intro i
    simpa only [Z, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left (integral_maskedFourierBilinearAmplitude_sq_le
        ρ₁ ρ₂ X Y (hb₁ i) (hb₂ i) (hbound₁ i) (hbound₂ i) hψ hψ₁ K v) (ha i)
  have hsZ : Summable (fun i ↦ a i *
      (∫ r in bilinearFrequencyWindow v, ‖Z i r‖ ^ 2)) :=
    (hsF.mul_left (2 * (ρ₁.real X * ρ₂.real Y))).of_nonneg_of_le
      (fun i ↦ mul_nonneg (ha i) (integral_nonneg (fun _ ↦ sq_nonneg _))) hweight
  calc
    _ ≤ (∑' i, a i) * ∑' i, a i * (∫ r in bilinearFrequencyWindow v, ‖Z i r‖ ^ 2) :=
      hbase
    _ ≤ (∑' i, a i) * ∑' i, 2 * (ρ₁.real X * ρ₂.real Y) *
        (a i * maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ i) (b₂ i) K v) :=
      mul_le_mul_of_nonneg_left
        (Summable.tsum_le_tsum hweight hsZ (hsF.mul_left _)) (tsum_nonneg ha)
    _ = _ := by rw [tsum_mul_left]; ring

end FalconerThetaGauge
