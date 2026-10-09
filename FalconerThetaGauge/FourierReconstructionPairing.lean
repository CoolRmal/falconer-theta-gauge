/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierReconstructionEnergy
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Actual smoothing and Fourier-band pairings

Fourier inversion and Fubini identify integration against the actual convolved measure
with integration against its concrete measure-Fourier multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter SchwartzMap FourierTransform
open scoped ENNReal Topology Convolution

namespace FalconerThetaGauge

/-- The frequency test obtained from a Schwartz smoothing kernel and a spatial test. -/
def schwartzKernelFrequencyTest (K φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 K) (𝓕⁻ φ)

@[simp] theorem schwartzKernelFrequencyTest_apply (K φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    schwartzKernelFrequencyTest K φ ξ = (𝓕 K) ξ * (𝓕⁻ φ) ξ := rfl

/-- The Fourier transform of the frequency test is the translated kernel test integral. -/
theorem fourier_schwartzKernelFrequencyTest (K φ : SchwartzMap ℝ ℂ) (z : ℝ) :
    (𝓕 (schwartzKernelFrequencyTest K φ)) z = ∫ x, K (x - z) * φ x := by
  let φneg : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv φ
  have hneg : 𝓕 φneg = 𝓕⁻ φ := by
    ext ξ
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_comp_neg]
    rfl
  let C := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φneg
  have hC : 𝓕 C = schwartzKernelFrequencyTest K φ := by
    rw [SchwartzMap.fourier_convolution, hneg]
    rfl
  have hInv : 𝓕⁻ (schwartzKernelFrequencyTest K φ) = C := by
    rw [← hC, fourierInv_fourier_eq]
  calc
    _ = (𝓕⁻ (schwartzKernelFrequencyTest K φ)) (-z) := by
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe,
        Real.fourierInv_eq_fourier_neg, neg_neg]
    _ = C (-z) := by rw [hInv]
    _ = ∫ x, K x * φ (z + x) := by
      rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        change K x * φ (-(-z - x)) = K x * φ (z + x)
        congr 2
        ring
    _ = _ := by
      simpa only [add_sub_cancel_left] using
        integral_add_left_eq_self (fun x ↦ K (x - z) * φ x) z

/-- The exact Fourier pairing identity for the actual smoothed measure. -/
theorem integral_schwartzMeasureDensity_mul_schwartz
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K φ : SchwartzMap ℝ ℂ) :
    (∫ x, schwartzMeasureDensity μ K x * φ x) =
      ∫ ξ, measureFourier μ ξ * (𝓕 K) ξ * (𝓕⁻ φ) ξ := by
  calc
    _ = ∫ z, ∫ x, K (x - z) * φ x ∂volume ∂μ :=
      integral_schwartzMeasureDensity_mul_test μ K φ.toBoundedContinuousFunction
    _ = ∫ z, (𝓕 (schwartzKernelFrequencyTest K φ)) z ∂μ := by
      simp_rw [fourier_schwartzKernelFrequencyTest]
    _ = ∫ ξ, measureFourier μ ξ * schwartzKernelFrequencyTest K φ ξ :=
      (integral_measureFourier_schwartz μ _).symm
    _ = _ := by simp_rw [schwartzKernelFrequencyTest_apply, mul_assoc]

/-- The actual frequency second-norm band has the same pairing as the actual smoothed band. -/
theorem integral_measureFourierBandL2_mul_schwartz
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    (∫ x, schwartzMeasureDensity μ (reconstructionBand n) x * φ x) =
      ∫ ξ, (𝓕⁻ φ) ξ * measureFourierBandL2 μ n ξ := by
  rw [integral_schwartzMeasureDensity_mul_schwartz]
  apply integral_congr_ae
  filter_upwards [measureFourierBandL2_coeFn μ n] with ξ hξ
  rw [hξ, measureFourierBand]
  ring

end FalconerThetaGauge
