/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaRootParts
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Genuine frequency Cauchy--Schwarz for the literal dyadic energy -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter

namespace FalconerThetaGauge

theorem dyadicFrequencyAverage_mul_le_sqrt (K v : ℕ) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf₀ : ∀ r ∈ Ioi 0, 0 ≤ f r) (hg₀ : ∀ r ∈ Ioi 0, 0 ≤ g r)
    (hff : Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r ^ 2))
    (hgg : Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * g r ^ 2)) :
    dyadicFrequencyAverage K v (fun r ↦ f r * g r) ≤
      Real.sqrt (dyadicFrequencyAverage K v (fun r ↦ f r ^ 2)) *
        Real.sqrt (dyadicFrequencyAverage K v (fun r ↦ g r ^ 2)) := by
  let cut := fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v)
  let F := fun r ↦ Real.sqrt (cut r) * f r
  let G := fun r ↦ Real.sqrt (cut r) * g r
  have hcut (r) : 0 ≤ cut r := (maskedFrequencyCutoff_mem_Icc K _).1
  have hmcut : Measurable cut := (contDiff_maskedFrequencyCutoff K).continuous.measurable.comp
    (measurable_id.div_const _)
  have hF : Measurable F := (Real.continuous_sqrt.measurable.comp hmcut).mul hf
  have hG : Measurable G := (Real.continuous_sqrt.measurable.comp hmcut).mul hg
  have heF (r) : F r ^ 2 = cut r * f r ^ 2 := by
    dsimp [F]; rw [mul_pow, Real.sq_sqrt (hcut r)]
  have heG (r) : G r ^ 2 = cut r * g r ^ 2 := by
    dsimp [G]; rw [mul_pow, Real.sq_sqrt (hcut r)]
  have hFG (r) : F r * G r = cut r * (f r * g r) := by
    dsimp [F, G]
    calc
      _ = (Real.sqrt (cut r)) ^ 2 * (f r * g r) := by ring
      _ = _ := by rw [Real.sq_sqrt (hcut r)]
  have hFm : MemLp F 2 (volume.restrict (Ioi 0)) :=
    (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr
      (hff.integrableOn.congr (Eventually.of_forall (fun r ↦ (heF r).symm)))
  have hGm : MemLp G 2 (volume.restrict (Ioi 0)) :=
    (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mpr
      (hgg.integrableOn.congr (Eventually.of_forall (fun r ↦ (heG r).symm)))
  have hF₀ : 0 ≤ᵐ[volume.restrict (Ioi 0)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.sqrt_nonneg _) (hf₀ r hr)
  have hG₀ : 0 ≤ᵐ[volume.restrict (Ioi 0)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.sqrt_nonneg _) (hg₀ r hr)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hF₀ hG₀
    (by simpa using hFm) (by simpa using hGm)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, heF, heG, hFG] at hCS
  unfold dyadicFrequencyAverage
  calc
    _ ≤ ((2 : ℝ) ^ v)⁻¹ *
        (Real.sqrt (∫ r in Ioi 0, cut r * f r ^ 2) *
          Real.sqrt (∫ r in Ioi 0, cut r * g r ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      have hroot : Real.sqrt (((2 : ℝ) ^ v)⁻¹) ^ 2 = ((2 : ℝ) ^ v)⁻¹ :=
        Real.sq_sqrt (by positivity)
      calc
        _ = Real.sqrt (((2 : ℝ) ^ v)⁻¹) ^ 2 *
            (Real.sqrt (∫ r in Ioi 0, cut r * f r ^ 2) *
              Real.sqrt (∫ r in Ioi 0, cut r * g r ^ 2)) := by rw [hroot]
        _ = _ := by dsimp only [cut]; ring

theorem maskedFourierEnergy_le_sqrt_self (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    maskedFourierEnergy ρ₁ ρ₂ X Y b₁ b₂ K v ≤
      Real.sqrt (maskedFourierEnergy ρ₁ ρ₁ X X b₁ b₁ K v) *
        Real.sqrt (maskedFourierEnergy ρ₂ ρ₂ Y Y b₂ b₂ K v) := by
  have hff := integrable_maskedFourierEnergy_integrand ρ₁ ρ₁ X X hb₁ hb₁
    hbound₁ hbound₁ K v
  have hgg := integrable_maskedFourierEnergy_integrand ρ₂ ρ₂ Y Y hb₂ hb₂
    hbound₂ hbound₂ K v
  simpa only [maskedFourierEnergy, ← sq] using dyadicFrequencyAverage_mul_le_sqrt K v
    (measurable_maskedCircularSpectrum ρ₁ X hb₁)
    (measurable_maskedCircularSpectrum ρ₂ Y hb₂)
    (fun _r hr ↦ maskedCircularSpectrum_nonneg ρ₁ X b₁ hr.le)
    (fun _r hr ↦ maskedCircularSpectrum_nonneg ρ₂ Y b₂ hr.le)
    (by simpa only [← sq] using hff) (by simpa only [← sq] using hgg)

end FalconerThetaGauge
