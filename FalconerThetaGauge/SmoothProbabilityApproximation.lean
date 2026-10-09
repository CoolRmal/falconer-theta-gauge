/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.SmoothMeasureApproximation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Weak convergence of the actual smoothed source probabilities

Normalized bumps form an approximate identity. Testing the measure convolution against
bounded continuous functions and applying dominated convergence recovers the original source.
These arguments adapt `FalconerPacking.SmoothProbabilityApproximation` (Yongxi Lin, Apache 2.0)
at commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/SmoothProbabilityApproximation.lean
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal ContDiff Convolution Topology

namespace FalconerThetaGauge

/-- The actual source probability convolved with a normalized smooth bump. -/
def smoothSourceProbability (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  ⟨(μ : Measure (EuclideanSpace ℝ (Fin 2))) ∗ smoothBumpMeasure φ, inferInstance⟩

/-- Symmetry of the bump identifies translation averages with the standard approximate identity. -/
theorem integral_smoothBumpMeasure_add
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    (∫ y, g (x + y) ∂smoothBumpMeasure φ) =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  rw [smoothBumpMeasure, integral_withDensity_eq_integral_toReal_smul₀
    φ.continuous_normed.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) (fun y ↦ g (x + y))]
  simp_rw [ENNReal.toReal_ofReal (φ.nonneg_normed _)]
  rw [← integral_neg_eq_self (fun y ↦ φ.normed volume y • g (x + y))]
  simp only [φ.normed_neg, sub_eq_add_neg, convolution, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]

/-- Shrinking normalized bumps converge weakly after convolution with any source probability. -/
theorem tendsto_smoothSourceProbability
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
    (hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n ↦ smoothSourceProbability μ (φ n)) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hm : StronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2) ↦ g (p.1 + p.2)) :=
    (g.continuous.comp (continuous_fst.add continuous_snd)).stronglyMeasurable
  have hlim (x : EuclideanSpace ℝ (Fin 2)) :
      Tendsto (fun n ↦ ∫ y, g (x + y) ∂smoothBumpMeasure (φ n)) atTop (𝓝 (g x)) := by
    simp_rw [integral_smoothBumpMeasure_add]
    exact ContDiffBump.convolution_tendsto_right_of_continuous hφ g.continuous x
  have hb (n : ℕ) : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))),
      ‖∫ y, g (x + y) ∂smoothBumpMeasure (φ n)‖ ≤ ‖g‖ := by
    exact Eventually.of_forall fun x ↦ by
      simpa using norm_integral_le_of_norm_le_const
        (μ := smoothBumpMeasure (φ n)) (Eventually.of_forall fun y ↦ g.norm_coe_le_norm (x + y))
  have h := tendsto_integral_of_dominated_convergence (μ := (μ : Measure _)) (fun _ ↦ ‖g‖)
    (fun n ↦ (hm.integral_prod_right' (ν := smoothBumpMeasure (φ n))).aestronglyMeasurable)
    (integrable_const _) hb (Eventually.of_forall hlim)
  convert h using 1
  funext n
  change (∫ x, g x ∂((μ : Measure _) ∗ smoothBumpMeasure (φ n))) = _
  exact integral_conv (g.integrable (μ := (μ : Measure _) ∗ smoothBumpMeasure (φ n)))

/-- A specific sequence of smooth bumps with outer radii tending to zero. -/
def shrinkingSourceBump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) where
  rIn := 1 / (2 * (n + 1 : ℝ))
  rOut := 1 / (n + 1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · have : (0 : ℝ) < n + 1 := by positivity
      linarith

theorem tendsto_shrinkingSourceBump_rOut :
    Tendsto (fun n ↦ (shrinkingSourceBump n).rOut) atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The explicitly chosen smooth source sequence converges to the original probability. -/
theorem tendsto_shrinking_smoothSourceProbability
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) :
    Tendsto (fun n ↦ smoothSourceProbability μ (shrinkingSourceBump n)) atTop (𝓝 μ) :=
  tendsto_smoothSourceProbability μ shrinkingSourceBump tendsto_shrinkingSourceBump_rOut

/-- The bump probability is carried by its open support ball. -/
theorem smoothBumpMeasure_compl_ball
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    smoothBumpMeasure φ (Metric.ball 0 φ.rOut)ᶜ = 0 := by
  rw [smoothBumpMeasure, withDensity_apply _ measurableSet_ball.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
  have hx' : x ∉ support (φ.normed volume) := by rwa [φ.support_normed_eq]
  simp only [notMem_support.mp hx', ENNReal.ofReal_zero, Pi.zero_apply]

/-- Source and bump support bounds add under convolution. -/
theorem ae_norm_le_smoothSourceProbability
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) {M : ℝ}
    (hμ : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))), ‖x‖ ≤ M) :
    ∀ᵐ x ∂(smoothSourceProbability μ φ : Measure (EuclideanSpace ℝ (Fin 2))),
      ‖x‖ ≤ M + φ.rOut := by
  have hφ : ∀ᵐ y ∂smoothBumpMeasure φ, ‖y‖ ≤ φ.rOut := by
    have h := (ae_iff.mpr (smoothBumpMeasure_compl_ball φ))
    filter_upwards [h] with y hy
    simpa only [dist_zero_right] using (Metric.mem_ball.mp hy).le
  change ∀ᵐ x ∂((μ : Measure _) ∗ smoothBumpMeasure φ), ‖x‖ ≤ M + φ.rOut
  rw [Measure.conv, ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)).mpr
  exact hμ.mono fun x hx ↦ hφ.mono fun y hy ↦ (norm_add_le x y).trans (add_le_add hx hy)

/-- Smoothing uniformly preserves every finite logarithmic Fourier energy. -/
theorem logarithmicFourierEnergy_smoothSourceProbability_le
    (γ : ℝ) (μ : ProbabilityMeasure Plane) (φ : ContDiffBump (0 : Plane)) :
    logarithmicFourierEnergy γ (smoothSourceProbability μ φ : Measure Plane) ≤
      logarithmicFourierEnergy γ (μ : Measure Plane) :=
  logarithmicFourierEnergy_conv_le γ _ _

end FalconerThetaGauge
