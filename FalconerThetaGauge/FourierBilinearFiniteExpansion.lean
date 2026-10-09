/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierBilinearFrequencyWindow
public import FalconerThetaGauge.FourierBilinearCoefficientSum

/-! # Integrated coefficient bounds for genuine finite masked Fourier expansions -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Finset

namespace FalconerThetaGauge

theorem integral_norm_sum_sq_le_weighted {ι : Type*} (s : Finset ι)
    {c z : ι → ℝ → ℂ} {a : ι → ℝ} {W : Set ℝ} (hW : MeasurableSet W)
    (hc : ∀ i ∈ s, Measurable (c i)) (hz : ∀ i ∈ s, Measurable (z i))
    (hzi : ∀ i ∈ s, IntegrableOn (fun r ↦ ‖z i r‖ ^ 2) W)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hca : ∀ i ∈ s, ∀ r ∈ W, ‖c i r‖ ≤ a i) :
    (∫ r in W, ‖∑ i ∈ s, c i r * z i r‖ ^ 2) ≤
      (∑ i ∈ s, a i) * ∑ i ∈ s, a i * (∫ r in W, ‖z i r‖ ^ 2) := by
  have hmajor : IntegrableOn (fun r ↦ (∑ i ∈ s, a i) *
      ∑ i ∈ s, a i * ‖z i r‖ ^ 2) W := by
    apply Integrable.const_mul
    exact integrable_finsetSum s (fun i hi ↦ (hzi i hi).const_mul (a i))
  have hpoint : ∀ r ∈ W, ‖∑ i ∈ s, c i r * z i r‖ ^ 2 ≤
      (∑ i ∈ s, a i) * ∑ i ∈ s, a i * ‖z i r‖ ^ 2 := by
    intro r hr
    exact norm_sum_mul_sq_le_weighted s (fun i ↦ c i r) (fun i ↦ z i r)
      (fun i hi ↦ hca i hi r hr)
  have hint : IntegrableOn (fun r ↦ ‖∑ i ∈ s, c i r * z i r‖ ^ 2) W := by
    apply Integrable.mono hmajor
    · exact ((Finset.measurable_sum s (fun i hi ↦ (hc i hi).mul (hz i hi))).norm.pow_const
        2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hW] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sum_nonneg ha)
          (sum_nonneg (fun i hi ↦ mul_nonneg (ha i hi) (sq_nonneg _))))]
      exact hpoint r hr
  calc
    _ ≤ ∫ r in W, (∑ i ∈ s, a i) * ∑ i ∈ s, a i * ‖z i r‖ ^ 2 :=
      setIntegral_mono_on hint hmajor hW hpoint
    _ = (∑ i ∈ s, a i) * ∑ i ∈ s, a i * (∫ r in W, ‖z i r‖ ^ 2) := by
      rw [integral_const_mul, integral_finsetSum s
        (fun i hi ↦ (hzi i hi).const_mul (a i))]
      simp_rw [integral_const_mul]

/-- Step 3 for an actual finite family of built symbols; each summand pays its actual energy. -/
theorem integral_sum_maskedFourierBilinearAmplitude_sq_le {ι : Type*} (s : Finset ι)
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : ι → Plane → UnitCircle → ℝ}
    (hb₁ : ∀ i ∈ s, Measurable (uncurry (b₁ i)))
    (hb₂ : ∀ i ∈ s, Measurable (uncurry (b₂ i)))
    (hbound₁ : ∀ i ∈ s, ∀ x w, |b₁ i x w| ≤ 1)
    (hbound₂ : ∀ i ∈ s, ∀ x w, |b₂ i x w| ≤ 1) {ψ : UnitCircle → ℝ}
    (hψ : Measurable ψ) (hψ₁ : ∀ w, |ψ w| ≤ 1) (K v : ℕ)
    {c : ι → ℝ → ℂ} {a : ι → ℝ} (hc : ∀ i ∈ s, Measurable (c i))
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hca : ∀ i ∈ s, ∀ r ∈ bilinearFrequencyWindow v, ‖c i r‖ ≤ a i) :
    (∫ r in bilinearFrequencyWindow v,
      ‖∑ i ∈ s, c i r *
        maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y (b₁ i) (b₂ i) ψ r‖ ^ 2) ≤
      2 * (ρ₁.real X * ρ₂.real Y) * (∑ i ∈ s, a i) *
        ∑ i ∈ s, a i * maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ i) (b₂ i) K v := by
  have hbase := integral_norm_sum_sq_le_weighted s measurableSet_Icc hc
    (fun i hi ↦ measurable_maskedFourierBilinearAmplitude
      ρ₁ ρ₂ X Y (hb₁ i hi) (hb₂ i hi) hψ)
    (fun i hi ↦ integrableOn_maskedFourierBilinearAmplitude_sq
      ρ₁ ρ₂ X Y (hb₁ i hi) (hb₂ i hi) (hbound₁ i hi) (hbound₂ i hi) hψ hψ₁ K v)
    ha hca
  calc
    _ ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * ∫ r in bilinearFrequencyWindow v,
        ‖maskedFourierBilinearAmplitude ρ₁ ρ₂ X Y (b₁ i) (b₂ i) ψ r‖ ^ 2 := hbase
    _ ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i *
        (2 * (ρ₁.real X * ρ₂.real Y) *
          maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ i) (b₂ i) K v) := by
      apply mul_le_mul_of_nonneg_left _ (sum_nonneg ha)
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (integral_maskedFourierBilinearAmplitude_sq_le
          ρ₁ ρ₂ X Y (hb₁ i hi) (hb₂ i hi) (hbound₁ i hi) (hbound₂ i hi)
          hψ hψ₁ K v)
        (ha i hi)
    _ = (∑ i ∈ s, a i) * (2 * (ρ₁.real X * ρ₂.real Y) *
        ∑ i ∈ s, a i * maskedFourierEnergy ρ₁ ρ₂ X Y (b₁ i) (b₂ i) K v) := by
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by ring

end FalconerThetaGauge
