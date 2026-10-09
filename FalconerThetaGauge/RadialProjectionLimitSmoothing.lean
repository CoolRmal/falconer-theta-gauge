module

public import FalconerThetaGauge.SmoothProbabilityApproximation

/-!
# Small smooth sources retain the prepared separation

Convolution enlarges a centered source ball by exactly the outer radius of
the bump. Both the measure carrier and the pointwise nonzero smooth density
obey this bound. A fixed small shrinking sequence therefore permits the
closed-carrier joint convergence argument and the bounded-ray estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal Topology Convolution

namespace FalconerThetaGauge

/-- A genuine centered support bound for the smoothed probability. -/
theorem ae_dist_le_smoothSourceProbability
    (μ : ProbabilityMeasure Plane) (φ : ContDiffBump (0 : Plane)) (b : Plane) {M : ℝ}
    (hμ : ∀ᵐ y ∂(μ : Measure Plane), dist y b ≤ M) :
    ∀ᵐ x ∂(smoothSourceProbability μ φ : Measure Plane), dist x b ≤ M + φ.rOut := by
  have hφ : ∀ᵐ z ∂smoothBumpMeasure φ, ‖z‖ ≤ φ.rOut := by
    filter_upwards [ae_iff.mpr (smoothBumpMeasure_compl_ball φ)] with z hz
    simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le
  change ∀ᵐ x ∂((μ : Measure Plane) ∗ smoothBumpMeasure φ), dist x b ≤ M + φ.rOut
  rw [Measure.conv, ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [hμ] with y hy
  filter_upwards [hφ] with z hz
  have htri : dist (y + z) b ≤ dist y b + ‖z‖ := by
    rw [dist_eq_norm, show y + z - b = (y - b) + z by abel]
    exact norm_add_le _ _
  exact htri.trans (add_le_add hy hz)

/-- The actual smooth density vanishes outside the enlarged centered carrier. -/
theorem smoothMeasureDensity_normed_eq_zero_of_lt_dist
    (μ : ProbabilityMeasure Plane) (φ : ContDiffBump (0 : Plane)) (b : Plane) {M : ℝ}
    (hμ : ∀ᵐ y ∂(μ : Measure Plane), dist y b ≤ M) {x : Plane}
    (hx : M + φ.rOut < dist x b) :
    smoothMeasureDensity (μ : Measure Plane) (φ.normed volume) x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  have hfar : φ.rOut < dist x y := by linarith [dist_triangle x y b]
  apply notMem_support.mp
  rw [φ.support_normed_eq]
  intro hmem
  have hnear := Metric.mem_ball.mp hmem
  simp only [dist_zero_right, ← dist_eq_norm] at hnear
  exact (not_lt_of_ge hfar.le hnear)

/-- Nonzero smoothed density stays within the same genuine enlarged carrier. -/
theorem dist_le_of_smoothMeasureDensity_normed_ne_zero
    (μ : ProbabilityMeasure Plane) (φ : ContDiffBump (0 : Plane)) (b : Plane) {M : ℝ}
    (hμ : ∀ᵐ y ∂(μ : Measure Plane), dist y b ≤ M) {x : Plane}
    (hx : smoothMeasureDensity (μ : Measure Plane) (φ.normed volume) x ≠ 0) :
    dist x b ≤ M + φ.rOut := by
  by_contra h
  exact hx (smoothMeasureDensity_normed_eq_zero_of_lt_dist μ φ b hμ (not_le.mp h))

/-- A specific tiny smooth bump sequence for the separated prepared carriers. -/
def shrinkingRadialBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := 1 / (200 * (n + 1 : ℝ))
  rOut := 1 / (100 * (n + 1 : ℝ))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · have : (0 : ℝ) < n + 1 := by positivity
      linarith

theorem shrinkingRadialBump_rOut_le (n : ℕ) :
    (shrinkingRadialBump n).rOut ≤ 1 / 100 := by
  change 1 / (100 * ((n : ℝ) + 1)) ≤ 1 / 100
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem tendsto_shrinkingRadialBump_rOut :
    Tendsto (fun n ↦ (shrinkingRadialBump n).rOut) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((100 : ℝ)⁻¹)
  convert h using 1
  · funext n
    change 1 / (100 * ((n : ℝ) + 1)) = (100 : ℝ)⁻¹ * (1 / ((n : ℝ) + 1))
    rw [one_div, mul_inv, one_div]
  · simp

theorem tendsto_radial_smoothSourceProbability (μ : ProbabilityMeasure Plane) :
    Tendsto (fun n ↦ smoothSourceProbability μ (shrinkingRadialBump n)) atTop (𝓝 μ) :=
  tendsto_smoothSourceProbability μ shrinkingRadialBump tendsto_shrinkingRadialBump_rOut

end FalconerThetaGauge
