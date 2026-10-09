/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierReconstructionMeasure
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Concrete dyadic Fourier reconstruction kernels

A fixed smooth frequency cutoff is one on the unit interval and zero outside the
interval of radius two. Its inverse Fourier transform and its dilates give the
actual smoothing kernels used for summable reconstruction.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- A fixed real smooth cutoff, with inner radius one and outer radius two. -/
def reconstructionFrequencyBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The fixed frequency cutoff as a complex Schwartz function. -/
def reconstructionFrequencyCutoff : SchwartzMap ℝ ℂ :=
  (reconstructionFrequencyBump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp reconstructionFrequencyBump.contDiff)

theorem reconstructionFrequencyCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) :
    reconstructionFrequencyCutoff x = 1 := by
  change (reconstructionFrequencyBump x : ℂ) = 1
  rw [reconstructionFrequencyBump.one_of_mem_closedBall]
  · norm_num
  · simpa [Metric.mem_closedBall, reconstructionFrequencyBump, Real.dist_eq] using hx

theorem reconstructionFrequencyCutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) :
    reconstructionFrequencyCutoff x = 0 := by
  change (reconstructionFrequencyBump x : ℂ) = 0
  rw [reconstructionFrequencyBump.zero_of_le_dist]
  · norm_num
  · simpa [reconstructionFrequencyBump, Real.dist_eq] using hx

theorem norm_reconstructionFrequencyCutoff_le_one (x : ℝ) :
    ‖reconstructionFrequencyCutoff x‖ ≤ 1 := by
  change ‖(reconstructionFrequencyBump x : ℂ)‖ ≤ 1
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (reconstructionFrequencyBump.nonneg (x := x))] using
    reconstructionFrequencyBump.le_one (x := x)

/-- The inverse Fourier transform of the fixed frequency cutoff. -/
def reconstructionKernel : SchwartzMap ℝ ℂ := 𝓕⁻ reconstructionFrequencyCutoff

theorem fourier_reconstructionKernel :
    𝓕 reconstructionKernel = reconstructionFrequencyCutoff :=
  fourier_fourierInv_eq _

theorem integral_reconstructionKernel : (∫ x, reconstructionKernel x) = 1 := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ ↦ f 0) fourier_reconstructionKernel
  simpa [SchwartzMap.fourier_coe, Real.fourier_real_eq,
    reconstructionFrequencyCutoff_eq_one (by norm_num : |(0 : ℝ)| ≤ 1)] using h

/-- Dilation of the line by a nonzero real number. -/
def reconstructionDilation (a : ℝ) (ha : a ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 a ha)

@[simp] theorem reconstructionDilation_apply (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    reconstructionDilation a ha x = a * x := rfl

/-- A mass-preserving spatial dilation of a Schwartz function. -/
def dilatedReconstructionKernel (a : ℝ) (ha : 0 < a) : SchwartzMap ℝ ℂ :=
  a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (reconstructionDilation a ha.ne') reconstructionKernel

@[simp] theorem dilatedReconstructionKernel_apply (a : ℝ) (ha : 0 < a) (x : ℝ) :
    dilatedReconstructionKernel a ha x = a • reconstructionKernel (a * x) := rfl

theorem integral_norm_dilatedReconstructionKernel (a : ℝ) (ha : 0 < a) :
    (∫ x, ‖dilatedReconstructionKernel a ha x‖) = ∫ x, ‖reconstructionKernel x‖ := by
  simp_rw [dilatedReconstructionKernel_apply, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun x ↦ ‖reconstructionKernel x‖) a]
  simp [abs_of_pos (inv_pos.mpr ha), smul_eq_mul, ha.ne']

theorem integral_dilatedReconstructionKernel (a : ℝ) (ha : 0 < a) :
    (∫ x, dilatedReconstructionKernel a ha x) = 1 := by
  simp_rw [dilatedReconstructionKernel_apply]
  rw [integral_smul, Measure.integral_comp_mul_left]
  simp [abs_of_pos (inv_pos.mpr ha), ha.ne', integral_reconstructionKernel]

/-- The actual spatial dilation has the prescribed rescaled Fourier multiplier. -/
theorem fourier_dilatedReconstructionKernel (a : ℝ) (ha : 0 < a) (ξ : ℝ) :
    (𝓕 (dilatedReconstructionKernel a ha)) ξ =
      reconstructionFrequencyCutoff (a⁻¹ * ξ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp_rw [dilatedReconstructionKernel_apply]
  calc
    _ = a • ∫ x, Real.fourierChar (-(x * ξ)) • reconstructionKernel (a * x) := by
      rw [← integral_smul]
      congr 1
      funext x
      exact smul_comm _ _ _
    _ = a • ∫ x, Real.fourierChar (-((a * x) * (a⁻¹ * ξ))) •
        reconstructionKernel (a * x) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        field_simp
    _ = a • (|a⁻¹| • ∫ y, Real.fourierChar (-(y * (a⁻¹ * ξ))) •
        reconstructionKernel y) := by
      rw [Measure.integral_comp_mul_left
        (fun y ↦ Real.fourierChar (-(y * (a⁻¹ * ξ))) • reconstructionKernel y) a]
    _ = (𝓕 reconstructionKernel) (a⁻¹ * ξ) := by
      rw [smul_smul, abs_of_pos (inv_pos.mpr ha), mul_inv_cancel₀ ha.ne', one_smul,
        ← Real.fourier_real_eq, ← SchwartzMap.fourier_coe]
    _ = _ := by rw [fourier_reconstructionKernel]

/-- Spatial frequency scale corresponding to characteristic-function dyadic radius `2^n`. -/
def reconstructionScale (n : ℕ) : ℝ := (2 : ℝ) ^ n / (2 * Real.pi)

theorem reconstructionScale_pos (n : ℕ) : 0 < reconstructionScale n := by
  exact div_pos (pow_pos (by norm_num) _) (mul_pos (by norm_num) Real.pi_pos)

/-- The actual low-pass kernel at dyadic frequency scale `n`. -/
def reconstructionLowpass (n : ℕ) : SchwartzMap ℝ ℂ :=
  dilatedReconstructionKernel (reconstructionScale n) (reconstructionScale_pos n)

/-- The difference between consecutive actual low-pass kernels. -/
def reconstructionBand (n : ℕ) : SchwartzMap ℝ ℂ :=
  reconstructionLowpass (n + 1) - reconstructionLowpass n

theorem fourier_reconstructionLowpass (n : ℕ) (ξ : ℝ) :
    (𝓕 (reconstructionLowpass n)) ξ =
      reconstructionFrequencyCutoff ((2 * Real.pi * ξ) / (2 : ℝ) ^ n) := by
  rw [reconstructionLowpass, fourier_dilatedReconstructionKernel]
  congr 1
  simp only [reconstructionScale, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem integral_norm_reconstructionLowpass (n : ℕ) :
    (∫ x, ‖reconstructionLowpass n x‖) = ∫ x, ‖reconstructionKernel x‖ :=
  integral_norm_dilatedReconstructionKernel _ _

/-- The dyadic band kernels have a uniform, concrete first-norm bound. -/
theorem integral_norm_reconstructionBand_le (n : ℕ) :
    (∫ x, ‖reconstructionBand n x‖) ≤ 2 * ∫ x, ‖reconstructionKernel x‖ := by
  calc
    _ ≤ ∫ x, ‖reconstructionLowpass (n + 1) x‖ + ‖reconstructionLowpass n x‖ := by
      apply integral_mono (reconstructionBand n).integrable.norm
        ((reconstructionLowpass (n + 1)).integrable.norm.add
          (reconstructionLowpass n).integrable.norm)
      exact fun x ↦ norm_sub_le _ _
    _ = _ := by
      rw [integral_add (reconstructionLowpass (n + 1)).integrable.norm
        (reconstructionLowpass n).integrable.norm,
        integral_norm_reconstructionLowpass, integral_norm_reconstructionLowpass]
      ring

theorem fourier_reconstructionLowpass_eq_one {n : ℕ} {ξ : ℝ}
    (hξ : |2 * Real.pi * ξ| ≤ (2 : ℝ) ^ n) :
    (𝓕 (reconstructionLowpass n)) ξ = 1 := by
  rw [fourier_reconstructionLowpass]
  apply reconstructionFrequencyCutoff_eq_one
  rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n),
    div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  exact hξ

theorem fourier_reconstructionLowpass_eq_zero {n : ℕ} {ξ : ℝ}
    (hξ : (2 : ℝ) ^ (n + 1) ≤ |2 * Real.pi * ξ|) :
    (𝓕 (reconstructionLowpass n)) ξ = 0 := by
  rw [fourier_reconstructionLowpass]
  apply reconstructionFrequencyCutoff_eq_zero
  rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n),
    le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  simpa [pow_succ, mul_comm] using hξ

theorem fourier_reconstructionBand (n : ℕ) :
    𝓕 (reconstructionBand n) =
      𝓕 (reconstructionLowpass (n + 1)) - 𝓕 (reconstructionLowpass n) := by
  exact (SchwartzMap.fourierTransformCLM ℂ).map_sub _ _

theorem norm_fourier_reconstructionBand_le (n : ℕ) (ξ : ℝ) :
    ‖(𝓕 (reconstructionBand n)) ξ‖ ≤ 2 := by
  rw [fourier_reconstructionBand]
  exact (norm_sub_le _ _).trans (by
    rw [fourier_reconstructionLowpass, fourier_reconstructionLowpass]
    have h₁ := norm_reconstructionFrequencyCutoff_le_one
      ((2 * Real.pi * ξ) / (2 : ℝ) ^ (n + 1))
    have h₂ := norm_reconstructionFrequencyCutoff_le_one
      ((2 * Real.pi * ξ) / (2 : ℝ) ^ n)
    linarith)

/-- The actual dyadic multiplier vanishes off its stated characteristic-frequency shell. -/
theorem fourier_reconstructionBand_support (n : ℕ) (ξ : ℝ)
    (hξ : (𝓕 (reconstructionBand n)) ξ ≠ 0) :
    2 * Real.pi * ξ ∈ dyadicFrequencyShell (n + 1) := by
  have hlower : (2 : ℝ) ^ n ≤ |2 * Real.pi * ξ| := by
    by_contra h
    have hle : |2 * Real.pi * ξ| ≤ (2 : ℝ) ^ n := (lt_of_not_ge h).le
    have hnext : |2 * Real.pi * ξ| ≤ (2 : ℝ) ^ (n + 1) :=
      hle.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
    apply hξ
    rw [fourier_reconstructionBand]
    simp [fourier_reconstructionLowpass_eq_one hle,
      fourier_reconstructionLowpass_eq_one hnext]
  have hupper : |2 * Real.pi * ξ| ≤ (2 : ℝ) ^ (n + 2) := by
    by_contra h
    have hle : (2 : ℝ) ^ (n + 2) ≤ |2 * Real.pi * ξ| := (lt_of_not_ge h).le
    have hprev : (2 : ℝ) ^ (n + 1) ≤ |2 * Real.pi * ξ| :=
      (pow_le_pow_right₀ (by norm_num) (by omega : n + 1 ≤ n + 2)).trans hle
    apply hξ
    rw [fourier_reconstructionBand]
    simp [fourier_reconstructionLowpass_eq_zero hprev,
      fourier_reconstructionLowpass_eq_zero (by simpa [Nat.add_assoc] using hle)]
  constructor
  · simpa [dyadicFrequencyShell, Nat.cast_add, zpow_natCast] using hlower
  · have hcast : (n + 1 : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by omega
    change |2 * Real.pi * ξ| ≤ (2 : ℝ) ^ ((((n + 1 : ℕ) : ℤ)) + 1)
    rw [Nat.cast_add, Nat.cast_one, hcast, zpow_natCast]
    exact hupper

end FalconerThetaGauge
