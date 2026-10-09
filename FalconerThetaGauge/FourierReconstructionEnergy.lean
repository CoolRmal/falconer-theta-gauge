/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
The Fourier duality proof adapts the FalconerPacking Fourier density proof.
-/
module

public import FalconerThetaGauge.FourierReconstructionApproximation
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Square-summable concrete Fourier bands of finite measures

The frequency bands are actual products of measure Fourier integrals and the Fourier
multipliers of the reconstruction kernels. Finite overlap and the specified shell energy
control their series in the complete square-norm space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter SchwartzMap FourierTransform
open scoped ENNReal Topology Classical

namespace FalconerThetaGauge

/-- The Fourier transform of a finite measure in mathlib's `2π` normalization. -/
def measureFourier (μ : Measure ℝ) (ξ : ℝ) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ ℝ) 1 ξ

/-- This normalization is obtained from the characteristic function by a frequency dilation. -/
theorem measureFourier_eq_charFun (μ : Measure ℝ) (ξ : ℝ) :
    measureFourier μ ξ = charFun μ (-2 * Real.pi * ξ) := by
  simp only [measureFourier, VectorFourier.fourierIntegral, innerₗ_apply_apply,
    Real.inner_apply, Circle.smul_def, Pi.one_apply, Real.fourierChar_apply, smul_eq_mul, mul_one,
    charFun_apply_real]
  congr 1
  funext x
  congr 1
  push_cast
  ring

theorem continuous_measureFourier (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (measureFourier μ) := by
  change Continuous (fun ξ ↦ measureFourier μ ξ)
  simp_rw [measureFourier_eq_charFun]
  exact continuous_charFun.comp (continuous_const.mul continuous_id)

/-- Fubini's identity holds for the actual measure Fourier integral. -/
theorem integral_measureFourier_schwartz (μ : Measure ℝ) [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℂ) :
    ∫ ξ, measureFourier μ ξ * φ ξ = ∫ x, (𝓕 φ) x ∂μ := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := μ) (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner (integrable_const (1 : ℂ)) φ.integrable
  simpa only [hflip, measureFourier, smul_eq_mul, Pi.one_apply, one_mul,
    SchwartzMap.fourier_coe] using! h

/-- Fourier inversion on the test function identifies integration against the measure. -/
theorem integral_schwartz_eq_measureFourier (μ : Measure ℝ) [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℂ) :
    ∫ x, φ x ∂μ = ∫ ξ, measureFourier μ ξ * (𝓕⁻ φ) ξ := by
  rw [integral_measureFourier_schwartz, fourier_fourierInv_eq]

/-- Cauchy--Schwarz for the integral of a product, expressed through `eLpNorm`. -/
theorem norm_integral_mul_le_eLpNorm_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖∫ x, f x * g x‖ ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    hg.aestronglyMeasurable hf.aestronglyMeasurable
  have hnorm : ‖∫ x, f x * g x‖ₑ ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    rw [eLpNorm_one_eq_lintegral_enorm
      (hg.aestronglyMeasurable.smul hf.aestronglyMeasurable)] at h
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, mul_comm] using h
  have hfin : eLpNorm f 2 volume * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, toReal_enorm] using ENNReal.toReal_mono hfin hnorm


/-- The actual frequency band of a finite measure. -/
def measureFourierBand (μ : Measure ℝ) (n : ℕ) (ξ : ℝ) : ℂ :=
  measureFourier μ ξ * (𝓕 (reconstructionBand n)) ξ

theorem memLp_measureFourierBand (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    MemLp (measureFourierBand μ n) 2 volume := by
  apply (((𝓕 (reconstructionBand n)).memLp 2 volume).norm.const_mul
    (μ.real univ)).mono'
    ((continuous_measureFourier μ).mul (𝓕 (reconstructionBand n)).continuous).aestronglyMeasurable
  exact Eventually.of_forall fun ξ ↦ by
    change ‖measureFourier μ ξ * (𝓕 (reconstructionBand n)) ξ‖ ≤ _
    rw [norm_mul, measureFourier_eq_charFun]
    exact mul_le_mul_of_nonneg_right (norm_charFun_le _) (norm_nonneg _)

/-- The actual band as an element of the complete square-norm space. -/
def measureFourierBandL2 (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_measureFourierBand μ n).toLp (measureFourierBand μ n)

theorem measureFourierBandL2_coeFn (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    measureFourierBandL2 μ n =ᵐ[volume] measureFourierBand μ n :=
  (memLp_measureFourierBand μ n).coeFn_toLp

theorem measurableSet_dyadicFrequencyShell (n : ℕ) :
    MeasurableSet (dyadicFrequencyShell n) :=
  (isClosed_le continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

/-- The exact shell energy in the manuscript's characteristic-function normalization. -/
def dyadicMeasureFourierEnergy (μ : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ r in dyadicFrequencyShell n, ‖charFun μ (-r)‖ ^ 2

theorem integrableOn_dyadicMeasureFourierEnergy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    IntegrableOn (fun r ↦ ‖charFun μ (-r)‖ ^ 2) (dyadicFrequencyShell n) volume := by
  apply ((continuous_charFun.comp continuous_neg).norm.pow 2).integrableOn_Icc.mono_set
    (t := Icc (-(2 : ℝ) ^ ((n : ℤ) + 1)) ((2 : ℝ) ^ ((n : ℤ) + 1)))
  intro r hr
  exact abs_le.mp hr.2

theorem measureFourierBand_norm_sq_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (ξ : ℝ) :
    ‖measureFourierBand μ n ξ‖ ^ 2 ≤
      4 * (dyadicFrequencyShell (n + 1)).indicator
        (fun r ↦ ‖charFun μ (-r)‖ ^ 2) (2 * Real.pi * ξ) := by
  by_cases hzero : (𝓕 (reconstructionBand n)) ξ = 0
  · simp only [measureFourierBand, hzero, mul_zero, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)
  · rw [indicator_of_mem (fourier_reconstructionBand_support n ξ hzero)]
    have hnorm := norm_fourier_reconstructionBand_le n ξ
    have hnonneg := norm_nonneg ((𝓕 (reconstructionBand n)) ξ)
    simp only [measureFourierBand, norm_mul, mul_pow, measureFourier_eq_charFun]
    have harg : -2 * Real.pi * ξ = -(2 * Real.pi * ξ) := by ring
    rw [harg]
    have hsq : ‖(𝓕 (reconstructionBand n)) ξ‖ ^ 2 ≤ 4 := by nlinarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq
      (sq_nonneg ‖charFun μ (-(2 * Real.pi * ξ))‖)

/-- The concrete second-norm square is controlled by the exact source shell energy. -/
theorem norm_measureFourierBandL2_sq_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    ‖measureFourierBandL2 μ n‖ ^ 2 ≤
      (4 * (2 * Real.pi)⁻¹) * dyadicMeasureFourierEnergy μ (n + 1) := by
  let e : ℝ → ℝ := (dyadicFrequencyShell (n + 1)).indicator
    (fun r ↦ ‖charFun μ (-r)‖ ^ 2)
  have he : Integrable e :=
    (integrable_indicator_iff (measurableSet_dyadicFrequencyShell _)).mpr
      (integrableOn_dyadicMeasureFourierEnergy μ _)
  have hscaled : Integrable (fun ξ ↦ e (2 * Real.pi * ξ)) :=
    (integrable_comp_mul_left_iff e (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mpr he
  calc
    _ = ∫ ξ, ‖measureFourierBand μ n ξ‖ ^ 2 := by
      rw [l2_norm_sq_eq_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [measureFourierBandL2_coeFn μ n] with ξ hξ
      rw [hξ]
    _ ≤ ∫ ξ, 4 * e (2 * Real.pi * ξ) := by
      apply integral_mono ((memLp_two_iff_integrable_sq_norm
        (memLp_measureFourierBand μ n).aestronglyMeasurable).mp
          (memLp_measureFourierBand μ n)) (hscaled.const_mul 4)
      exact measureFourierBand_norm_sq_le μ n
    _ = _ := by
      rw [integral_const_mul, Measure.integral_comp_mul_left e (2 * Real.pi),
        abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
      simp only [smul_eq_mul, e, integral_indicator (measurableSet_dyadicFrequencyShell _),
        dyadicMeasureFourierEnergy]
      ring

/-- Summable source shell energies give a convergent series of the actual Fourier bands. -/
theorem summable_measureFourierBandL2
    (ν : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (ν n)] (N₀ : ℕ)
    (henergy : Summable (fun n ↦ dyadicMeasureFourierEnergy (ν n) (n + N₀ + 1))) :
    Summable (fun n ↦ measureFourierBandL2 (ν n) (n + N₀)) := by
  have hsquare : Summable (fun n ↦ ‖measureFourierBandL2 (ν n) (n + N₀)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
      (fun n ↦ norm_measureFourierBandL2_sq_le (ν n) (n + N₀))
      (henergy.mul_left (4 * (2 * Real.pi)⁻¹))
  apply summable_l2_of_finite_overlap _ (show 0 < 3 by decide) hsquare
  intro s
  filter_upwards [ae_all_iff.mpr (fun n ↦ measureFourierBandL2_coeFn (ν n) (n + N₀))]
    with ξ hξ
  let t := s.filter fun n ↦ measureFourierBandL2 (ν n) (n + N₀) ξ ≠ 0
  let u := (s.image fun n ↦ n + N₀ + 1).filter fun k ↦
    2 * Real.pi * ξ ∈ dyadicFrequencyShell k
  have hmap : ∀ n ∈ t, n + N₀ + 1 ∈ u := by
    intro n hn
    obtain ⟨hns, hnzero⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨n, hns, rfl⟩, ?_⟩
    apply fourier_reconstructionBand_support
    intro hzero
    apply hnzero
    rw [hξ n]
    simp [measureFourierBand, hzero]
  have hcard : t.card ≤ u.card := Finset.card_le_card_of_injOn
    (fun n ↦ n + N₀ + 1) hmap (fun n _ m _ hnm ↦ by
      change n + N₀ + 1 = m + N₀ + 1 at hnm
      omega)
  exact hcard.trans (card_dyadicFrequencyShell_indices_le _ _)

end FalconerThetaGauge
