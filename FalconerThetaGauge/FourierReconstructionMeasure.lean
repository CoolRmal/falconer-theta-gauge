/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
The convolution estimates adapt the FalconerPacking Schwartz measure reconstruction proofs.
-/
module

public import FalconerThetaGauge.SummableReconstruction
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# First-norm reconstruction of dominated finite measures

An actual Schwartz kernel convolved with a finite positive measure gives an integrable
function. Its first norm is bounded by the kernel first norm times the measure's mass.
For a dominated measure, subtraction is a positive measure whose mass is exactly the
removed mass. Thus uniformly first-norm-bounded kernels turn summable removed masses
into a convergent series of actual first-norm errors.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The actual convolution of a Schwartz kernel with a finite source measure on the line. -/
def schwartzMeasureDensity (μ : Measure ℝ) (K : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ z, K (x - z) ∂μ

theorem integrable_schwartzMeasureDensity_integrand
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun z ↦ K (x - z)) μ :=
  (integrable_const (SchwartzMap.seminorm ℝ 0 0 K)).mono'
    (K.continuous.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun _ ↦ K.norm_le_seminorm ℝ _)

theorem integrable_schwartzMeasureDensity_prod
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ × ℝ ↦ K (p.1 - p.2)) (volume.prod μ) := by
  simpa using (integrable_const (1 : ℂ) (μ := μ)).convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) K.integrable

theorem integrable_schwartzMeasureDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K : SchwartzMap ℝ ℂ) :
    Integrable (schwartzMeasureDensity μ K) volume :=
  (integrable_schwartzMeasureDensity_prod μ K).integral_prod_left

/-- The exact first-norm bound for the actual smoothed source. -/
theorem integral_norm_schwartzMeasureDensity_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K : SchwartzMap ℝ ℂ) :
    (∫ x, ‖schwartzMeasureDensity μ K x‖) ≤ μ.real univ * ∫ x, ‖K x‖ := by
  calc
    _ ≤ ∫ x, ∫ z, ‖K (x - z)‖ ∂μ ∂volume := by
      apply integral_mono (integrable_schwartzMeasureDensity μ K).norm
        (integrable_schwartzMeasureDensity_prod μ K).norm.integral_prod_left
      exact fun _ ↦ norm_integral_le_integral_norm _
    _ = ∫ z, ∫ x, ‖K (x - z)‖ ∂volume ∂μ :=
      integral_integral_swap (integrable_schwartzMeasureDensity_prod μ K).norm
    _ = _ := by
      simp_rw [integral_sub_right_eq_self (fun x ↦ ‖K x‖)]
      simp [smul_eq_mul]

/-- The corresponding element of the complete first-norm space. -/
def schwartzMeasureL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (K : SchwartzMap ℝ ℂ) :
    Lp ℂ 1 (volume : Measure ℝ) :=
  Integrable.toL1 (schwartzMeasureDensity μ K) (integrable_schwartzMeasureDensity μ K)

theorem schwartzMeasureL1_coeFn
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K : SchwartzMap ℝ ℂ) :
    schwartzMeasureL1 μ K =ᵐ[volume] schwartzMeasureDensity μ K :=
  Integrable.coeFn_toL1 _

theorem norm_schwartzMeasureL1_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K : SchwartzMap ℝ ℂ) :
    ‖schwartzMeasureL1 μ K‖ ≤ μ.real univ * ∫ x, ‖K x‖ := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, ‖schwartzMeasureDensity μ K x‖ := by
      apply integral_congr_ae
      filter_upwards [schwartzMeasureL1_coeFn μ K] with x hx
      rw [hx]
    _ ≤ _ := integral_norm_schwartzMeasureDensity_le μ K

/-- The positive remainder has exactly the mass removed by domination. -/
theorem real_mass_sub_measure (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) :
    (μ - ν).real univ = μ.real univ - ν.real univ := by
  simp only [Measure.real, Measure.sub_apply MeasurableSet.univ hν]
  exact ENNReal.toReal_sub_of_le (hν univ) (measure_ne_top μ univ)

/-- Smoothing commutes with subtraction of a dominated finite positive measure. -/
theorem schwartzMeasureDensity_sub_measure
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) (K : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzMeasureDensity (μ - ν) K x =
      schwartzMeasureDensity μ K x - schwartzMeasureDensity ν K x := by
  apply (eq_sub_iff_add_eq).mpr
  have h := integral_add_measure
    (integrable_schwartzMeasureDensity_integrand (μ - ν) K x)
    (integrable_schwartzMeasureDensity_integrand ν K x)
  rw [Measure.sub_add_cancel_of_le hν] at h
  exact h.symm

/-- The actual smoothed remainder has first norm bounded by the removed mass. -/
theorem norm_schwartzMeasureL1_sub_measure_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) (K : SchwartzMap ℝ ℂ) :
    ‖schwartzMeasureL1 (μ - ν) K‖ ≤
      (μ.real univ - ν.real univ) * ∫ x, ‖K x‖ := by
  simpa only [real_mass_sub_measure μ ν hν] using norm_schwartzMeasureL1_le (μ - ν) K

/-- Uniform kernel first norms and summable removed masses give summable actual errors. -/
theorem summable_norm_smoothed_remainders
    (μ : Measure ℝ) [IsFiniteMeasure μ] (ν : ℕ → Measure ℝ)
    [∀ n, IsFiniteMeasure (ν n)] (hν : ∀ n, ν n ≤ μ)
    (K : ℕ → SchwartzMap ℝ ℂ) {C : ℝ}
    (hK : ∀ n, (∫ x, ‖K n x‖) ≤ C)
    (hremoved : Summable (fun n ↦ μ.real univ - (ν n).real univ)) :
    Summable (fun n ↦ ‖schwartzMeasureL1 (μ - ν n) (K n)‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ (norm_schwartzMeasureL1_sub_measure_le μ (ν n) (hν n) (K n)).trans ?_)
    (hremoved.mul_right C)
  exact mul_le_mul_of_nonneg_left (hK n)
    (by rw [← real_mass_sub_measure μ (ν n) (hν n)]; exact ENNReal.toReal_nonneg)

end FalconerThetaGauge
