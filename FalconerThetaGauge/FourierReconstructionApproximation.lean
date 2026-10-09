/-
Released under Apache 2.0 license as described in the file LICENSE.
The bounded-test reconstruction adapts the FalconerPacking reconstruction proof.
-/
module

public import FalconerThetaGauge.FourierReconstructionCutoff
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual low-pass reconstruction of finite measures on the line

The spatial kernels reconstruct every finite positive measure against bounded continuous
complex tests. The proof uses an explicit dilation identity and dominated convergence.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The exact complex test-integral formula for the convolved source. -/
theorem integral_schwartzMeasureDensity_mul_test
    (μ : Measure (ℝ)) [IsFiniteMeasure μ]
    (K : SchwartzMap (ℝ) ℂ)
    (g : BoundedContinuousFunction (ℝ) ℂ) :
    (∫ x, schwartzMeasureDensity μ K x * g x) =
      ∫ z, ∫ x, K (x - z) * g x ∂volume ∂μ := by
  have hi : Integrable (fun p : ℝ × ℝ ↦
      K (p.1 - p.2) * g p.1) (volume.prod μ) :=
    (integrable_schwartzMeasureDensity_prod μ K).mul_bdd
      (g.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ g.norm_coe_le_norm p.1)
  calc
    _ = ∫ x, ∫ z, K (x - z) * g x ∂μ ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_mul_const _ _).symm
    _ = _ := integral_integral_swap hi

/-- The exact dilation identity that makes the approximate-identity limit elementary. -/
theorem integral_dilatedReconstructionKernel_mul_test (a : ℝ) (ha : 0 < a)
    (z : ℝ) (g : ℝ → ℂ) :
    (∫ x, dilatedReconstructionKernel a ha (x - z) * g x) =
      ∫ w, reconstructionKernel w * g (z + a⁻¹ • w) := by
  let f (w : ℝ) :=
    reconstructionKernel w * g (z + a⁻¹ • w)
  calc
    _ = ∫ x, dilatedReconstructionKernel a ha x * g (z + x) := by
      simpa only [add_sub_cancel_left] using
        (integral_add_left_eq_self
          (fun x ↦ dilatedReconstructionKernel a ha (x - z) * g x) z).symm
    _ = a • ∫ x, f (a • x) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [dilatedReconstructionKernel_apply, f, smul_mul_assoc, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    _ = a • (|(a)⁻¹| • ∫ w, f w) := by
      simp_rw [smul_eq_mul]
      rw [Measure.integral_comp_mul_left f a]
    _ = _ := by
      rw [smul_smul, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_smul]

/-- Low-pass reconstruction against every bounded continuous complex test. -/
theorem tendsto_integral_lowpassMeasureDensity
    (μ : Measure (ℝ)) [IsFiniteMeasure μ]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hatop : Tendsto a atTop atTop)
    (g : BoundedContinuousFunction (ℝ) ℂ) :
    Tendsto (fun n ↦ ∫ x, schwartzMeasureDensity μ (dilatedReconstructionKernel (a n) (ha n)) x * g x)
      atTop (𝓝 (∫ z, g z ∂μ)) := by
  have hK : (∫ w, reconstructionKernel w) = 1 := by
    exact integral_reconstructionKernel
  have hinv : Tendsto (fun n ↦ (a n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hatop
  have hpoint (z : ℝ) :
      Tendsto (fun n ↦ ∫ w, reconstructionKernel w * g (z + (a n)⁻¹ • w))
        atTop (𝓝 (g z)) := by
    have h := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun n w ↦ reconstructionKernel w * g (z + (a n)⁻¹ • w))
      (f := fun w ↦ reconstructionKernel w * g z)
      (fun w ↦ ‖reconstructionKernel w‖ * ‖g‖)
      (fun n ↦ (show Continuous (fun w ↦ reconstructionKernel w *
        g (z + (a n)⁻¹ • w)) by fun_prop).aestronglyMeasurable)
      (reconstructionKernel.integrable.norm.mul_const ‖g‖)
      (fun n ↦ Eventually.of_forall fun w ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _))
      (Eventually.of_forall fun w ↦ tendsto_const_nhds.mul
        ((g.continuous.tendsto z).comp (by
          simpa using tendsto_const_nhds.add (hinv.smul_const w))))
    simpa only [integral_mul_const, hK, one_mul] using h
  have hbound (n : ℕ) (z : ℝ) :
      ‖∫ w, reconstructionKernel w * g (z + (a n)⁻¹ • w)‖ ≤
        (∫ w, ‖reconstructionKernel w‖) * ‖g‖ := by
    simpa only [integral_mul_const] using norm_integral_le_of_norm_le
      (reconstructionKernel.integrable.norm.mul_const ‖g‖)
      (Eventually.of_forall fun w ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _))
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n z ↦ ∫ w, reconstructionKernel w * g (z + (a n)⁻¹ • w))
    (f := fun z ↦ g z)
    (fun _ ↦ (∫ w, ‖reconstructionKernel w‖) * ‖g‖)
    (fun n ↦ (show Continuous (fun p : ℝ ×
      ℝ ↦ reconstructionKernel p.2 *
        g (p.1 + (a n)⁻¹ • p.2)) by
          fun_prop).stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
    (integrable_const _) (fun n ↦ Eventually.of_forall (hbound n))
    (Eventually.of_forall hpoint)
  convert h using 1
  funext n
  rw [integral_schwartzMeasureDensity_mul_test]
  simp_rw [integral_dilatedReconstructionKernel_mul_test]

theorem tendsto_reconstructionScale : Tendsto reconstructionScale atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_div_const
    (mul_pos (by norm_num) Real.pi_pos)

/-- Dyadic low-pass smoothing reconstructs the original finite measure on every Schwartz test. -/
theorem tendsto_integral_reconstructionLowpass_schwartz
    (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n ↦ ∫ x, schwartzMeasureDensity μ (reconstructionLowpass n) x * φ x)
      atTop (𝓝 (∫ z, φ z ∂μ)) := by
  exact tendsto_integral_lowpassMeasureDensity μ reconstructionScale_pos
    tendsto_reconstructionScale φ.toBoundedContinuousFunction


end FalconerThetaGauge
