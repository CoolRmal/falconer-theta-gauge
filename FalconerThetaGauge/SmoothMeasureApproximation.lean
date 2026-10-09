/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.OrliczEnergyFourier
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Smooth approximation of finite source measures

A compact smooth convolution kernel gives an actual smooth density. The corresponding
measure is the convolution of the source with the kernel measure, so probability kernels
decrease Fourier energy. These genuine convolution arguments adapt
`FalconerPacking.SmoothMeasureApproximation` (Yongxi Lin, Apache 2.0) at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/SmoothMeasureApproximation.lean
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal ContDiff Convolution

namespace FalconerThetaGauge

/-- Smooth a finite source by an ordinary convolution kernel. -/
def smoothMeasureDensity (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∫ y, φ (x - y) ∂μ

theorem integrable_smoothMeasureDensity_integrand
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hc : Continuous φ) (hk : HasCompactSupport φ)
    (x : EuclideanSpace ℝ (Fin 2)) : Integrable (fun y ↦ φ (x - y)) μ :=
  (hc.comp (by fun_prop)).integrable_of_hasCompactSupport
    (hk.comp_homeomorph (Homeomorph.subLeft x))

theorem smoothMeasureDensity_nonneg
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hpos : ∀ x, 0 ≤ φ x) (x) :
    0 ≤ smoothMeasureDensity μ φ x := integral_nonneg fun _ ↦ hpos _

/-- Smoothness of a compact kernel passes to convolution with an arbitrary finite source. -/
theorem contDiff_smoothMeasureDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hc : ContDiff ℝ ∞ φ)
    (hk : HasCompactSupport φ) : ContDiff ℝ ∞ (smoothMeasureDensity μ φ) := by
  have hz : ∀ p x : EuclideanSpace ℝ (Fin 2), p ∈ univ → x ∉ tsupport φ → φ x = 0 :=
    fun _ _ _ hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hg : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2) ↦ φ p.2) := hc.comp contDiff_snd
  have h := contDiffOn_convolution_right_with_param_comp
    (n := ⊤) (μ := μ) (ContinuousLinearMap.mul ℝ ℝ)
    (v := id) (s := univ) contDiffOn_id isOpen_univ hk.isCompact hz
    (show LocallyIntegrable (fun _ : EuclideanSpace ℝ (Fin 2) ↦ (1 : ℝ)) μ from
      (integrable_const 1).locallyIntegrable) hg.contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  funext x
  simp only [smoothMeasureDensity, convolution, ContinuousLinearMap.mul_apply', one_mul, id]

/-- The extended smooth density is the positive integral of the extended kernel. -/
theorem ofReal_smoothMeasureDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hc : Continuous φ) (hk : HasCompactSupport φ)
    (hpos : ∀ x, 0 ≤ φ x) (x : EuclideanSpace ℝ (Fin 2)) :
    ENNReal.ofReal (smoothMeasureDensity μ φ x) = ∫⁻ y, ENNReal.ofReal (φ (x - y)) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal (integrable_smoothMeasureDensity_integrand μ hc hk x)
    (Filter.Eventually.of_forall fun _ ↦ hpos _)

/-- The smooth density represents the actual convolution measure. -/
theorem withDensity_smoothMeasureDensity_eq_conv
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hc : ContDiff ℝ ∞ φ)
    (hk : HasCompactSupport φ) (hpos : ∀ x, 0 ≤ φ x) :
    volume.withDensity (fun x ↦ ENNReal.ofReal (smoothMeasureDensity μ φ x)) =
      μ ∗ volume.withDensity (fun x ↦ ENNReal.ofReal (φ x)) := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  have hd := (contDiff_smoothMeasureDensity μ hc hk).continuous.measurable.ennreal_ofReal
  have hφ := hc.continuous.measurable
  rw [lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable hg.aemeasurable,
    Measure.lintegral_conv hg]
  simp_rw [ofReal_smoothMeasureDensity μ hc.continuous hk hpos]
  calc
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (φ (x - y)) * g x ∂μ ∂volume := by
      apply lintegral_congr
      intro x
      rw [lintegral_mul_const _ (by fun_prop)]
      rfl
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (φ (x - y)) * g x ∂volume ∂μ := by
      apply lintegral_lintegral_swap
      exact ((hφ.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal.mul
        (hg.comp measurable_fst)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [lintegral_withDensity_eq_lintegral_mul₀ hc.continuous.measurable.ennreal_ofReal.aemeasurable
        (show AEMeasurable (fun x ↦ g (y + x)) volume from
          (hg.comp (measurable_const.add measurable_id)).aemeasurable)]
      have h := lintegral_add_left_eq_self (μ := volume)
        (fun x : EuclideanSpace ℝ (Fin 2) ↦ ENNReal.ofReal (φ (x - y)) * g x) y
      simpa only [add_sub_cancel_left, Pi.mul_apply] using h.symm

/-- Convolution with a probability kernel decreases the characteristic-function modulus. -/
theorem norm_charFun_conv_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (ξ : EuclideanSpace ℝ (Fin 2)) : ‖charFun (μ ∗ ν) ξ‖ ≤ ‖charFun μ ξ‖ := by
  rw [charFun_conv, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_charFun_le_one (μ := ν) ξ)

/-- Every nonnegative frequency weight inherits the same convolution contraction. -/
theorem lintegral_weighted_charFun_conv_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (w : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    ∫⁻ ξ, w ξ * ENNReal.ofReal (‖charFun (μ ∗ ν) ξ‖ ^ 2) ≤
      ∫⁻ ξ, w ξ * ENNReal.ofReal (‖charFun μ ξ‖ ^ 2) := by
  apply lintegral_mono
  intro ξ
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_conv_le μ ν ξ) 2

/-- Compact support of both the source and the kernel bounds the support of the smooth density. -/
theorem hasCompactSupport_smoothMeasureDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hk : HasCompactSupport φ)
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M) : HasCompactSupport (smoothMeasureDensity μ φ) := by
  obtain ⟨R, _, hR⟩ := hk.isCompact.isBounded.exists_pos_norm_le
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (M + R))
  intro x hx
  by_contra hout
  have hnorm : M + R < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le]
    using hout
  apply (mem_support.mp hx)
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  by_contra hφ
  have hxy := hR (x - y) (subset_tsupport _ (mem_support.mpr hφ))
  have htriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - y) y
  linarith

/-- A normalized smooth bump defines a compactly supported probability kernel. -/
def smoothBumpMeasure (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (φ.normed volume x))

instance smoothBumpMeasure.instIsProbabilityMeasure
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    IsProbabilityMeasure (smoothBumpMeasure φ) where
  measure_univ := by
    rw [smoothBumpMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
        (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]

/-- The source smoothed by a normalized bump is a genuine probability density. -/
theorem isProbabilityMeasure_smoothMeasureDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    IsProbabilityMeasure (volume.withDensity
      (fun x ↦ ENNReal.ofReal (smoothMeasureDensity μ (φ.normed volume) x))) := by
  rw [withDensity_smoothMeasureDensity_eq_conv μ φ.contDiff_normed φ.hasCompactSupport_normed
    φ.nonneg_normed]
  exact inferInstanceAs (IsProbabilityMeasure (μ ∗ smoothBumpMeasure φ))

/-- The literal logarithmically weighted Fourier energy decreases under probability smoothing. -/
theorem logarithmicFourierEnergy_conv_le (γ : ℝ)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] :
    logarithmicFourierEnergy γ (μ ∗ ν) ≤ logarithmicFourierEnergy γ μ := by
  unfold logarithmicFourierEnergy
  apply lintegral_mono
  intro ξ
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  simp only [norm_planarMeasureFourier]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_conv_le μ ν ξ) 2

end FalconerThetaGauge
