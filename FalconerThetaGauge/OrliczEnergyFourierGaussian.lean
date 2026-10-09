/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.Statement
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Planar Gaussian Fourier duality

The Fourier transform here has the manuscript's literal phase `exp(-i ξ · x)`.
The Gaussian duality proof adapts `FalconerPacking/GaussianEnergy.lean`
(Yongxi Lin, Apache 2.0). It uses Mathlib's evaluated Gaussian transform and
Fubini's theorem, with finite measures and explicit positive Gaussian scales.
-/

@[expose] public section

noncomputable section

open MeasureTheory ComplexConjugate
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

/-- The planar measure Fourier transform with phase `exp(-i ξ · x)`. -/
def planarMeasureFourier (μ : Measure Plane) (ξ : Plane) : ℂ := charFun μ (-ξ)

theorem planarMeasureFourier_eq_integral (μ : Measure Plane) (ξ : Plane) :
    planarMeasureFourier μ ξ = ∫ x, Complex.exp (-((⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) ∂μ := by
  simp only [planarMeasureFourier, charFun_apply, inner_neg_right, Complex.ofReal_neg]

theorem norm_planarMeasureFourier (μ : Measure Plane) (ξ : Plane) :
    ‖planarMeasureFourier μ ξ‖ = ‖charFun μ ξ‖ := by
  simp [planarMeasureFourier, charFun_neg]

@[fun_prop]
theorem continuous_planarMeasureFourier (μ : Measure Plane) [IsFiniteMeasure μ] :
    Continuous (planarMeasureFourier μ) := continuous_charFun.comp continuous_neg

theorem integral_planarGaussian_character {b : ℝ} (hb : 0 < b) (x : Plane) :
    ∫ ξ : Plane, Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) * Complex.exp (⟪x, ξ⟫ * Complex.I) =
      (Real.pi / b : ℝ) * Complex.exp (-(‖x‖ ^ 2 / (4 * b) : ℝ)) := by
  simp_rw [← Complex.exp_add, mul_comm (⟪x, _⟫ : ℂ) Complex.I]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by exact hb)]
  simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  norm_num
  ring_nf
  simp

theorem integrable_planarGaussian_character_kernel (μ : Measure Plane) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : Plane × Plane ↦
      Complex.exp (-(b : ℂ) * ‖p.1‖ ^ 2) * Complex.exp (⟪p.2, p.1⟫ * Complex.I))
      (volume.prod μ) := by
  have hg : Integrable (fun ξ : Plane ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2)) volume := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by exact hb : 0 < (b : ℂ).re) 0 (0 : Plane)
  apply (hg.comp_fst μ).mono (by fun_prop)
  exact Filter.Eventually.of_forall fun p ↦ by simp

theorem integral_planarGaussian_charFun (μ : Measure Plane) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    ∫ ξ : Plane, Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) * charFun μ ξ =
      (Real.pi / b : ℝ) * ∫ x, Complex.exp (-(‖x‖ ^ 2 / (4 * b) : ℝ)) ∂μ := by
  simp_rw [charFun_apply, ← integral_const_mul]
  rw [integral_integral_swap (integrable_planarGaussian_character_kernel μ hb)]
  simp_rw [integral_planarGaussian_character hb]

theorem charFun_difference_eq_norm_sq (μ : Measure Plane) [IsFiniteMeasure μ] (ξ : Plane) :
    charFun ((μ.prod μ).map (fun p ↦ p.1 - p.2)) ξ = (‖charFun μ ξ‖ ^ 2 : ℝ) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hphase (p : Plane × Plane) :
      Complex.exp (⟪p.1 - p.2, ξ⟫ * Complex.I) =
        Complex.exp (⟪p.1, ξ⟫ * Complex.I) * Complex.exp (⟪p.2, -ξ⟫ * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  simp_rw [hphase]
  rw [integral_prod_mul (fun x : Plane ↦ Complex.exp (⟪x, ξ⟫ * Complex.I))
    (fun x : Plane ↦ Complex.exp (⟪x, -ξ⟫ * Complex.I))]
  change charFun μ ξ * charFun μ (-ξ) = _
  rw [charFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Exact duality between Gaussian-weighted squared Fourier modulus and the positive
spatial Gaussian kernel, in the manuscript's Fourier normalization. -/
theorem integral_planarGaussian_fourier_norm_sq (μ : Measure Plane) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    ∫ ξ : Plane, Real.exp (-b * ‖ξ‖ ^ 2) * ‖planarMeasureFourier μ ξ‖ ^ 2 =
      Real.pi / b * ∫ p : Plane × Plane,
        Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * b))) ∂μ.prod μ := by
  have h := integral_planarGaussian_charFun ((μ.prod μ).map (fun p ↦ p.1 - p.2)) hb
  simp_rw [charFun_difference_eq_norm_sq] at h
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  have hexp (ξ : Plane) :
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) = (Real.exp (-b * ‖ξ‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  simp_rw [hexp] at h
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    integral_complex_ofReal] at h
  simpa only [norm_planarMeasureFourier] using Complex.ofReal_inj.mp h

end FalconerThetaGauge
