module

public import FalconerThetaGauge.RadialProjectionLimitSmoothing
public import FalconerThetaGauge.GaugeSeparatedMeasuresGeometry

/-!
# Separated carriers for the endpoint approximation

These concrete bounds use the actual preparation radii. Pins lie in a ball
of radius `1/400`, source smoothing lies in a ball of radius `1/80`, and their
centers are a quarter unit apart. Thus every approximating pair stays at
distance at least `1/5` and at most one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The prepared compact mass-one carrier gives the actual centered pin/source bound. -/
theorem ae_dist_le_of_compact_carrier (μ : ProbabilityMeasure Plane) {S : Set Plane}
    (hS : IsCompact S) (hmass : (μ : Measure Plane) S = 1) {a : Plane} {r : ℝ}
    (hsub : S ⊆ Metric.ball a r) : ∀ᵐ x ∂(μ : Measure Plane), dist x a ≤ r := by
  have hmem : ∀ᵐ x ∂(μ : Measure Plane), x ∈ S :=
    ae_iff.mpr ((prob_compl_eq_zero_iff hS.measurableSet).mpr hmass)
  filter_upwards [hmem] with x hx
  exact (Metric.mem_ball.mp (hsub hx)).le

/-- The true fixed separation and bounded distances of the approximation carriers. -/
theorem prepared_enlarged_balls_distance_bounds {a b x y : Plane}
    (hab : dist a b = 1 / 4) (hx : x ∈ Metric.closedBall a (1 / 400))
    (hy : y ∈ Metric.closedBall b (1 / 80)) :
    (1 / 5 : ℝ) ≤ dist x y ∧ dist x y ≤ 1 := by
  have hx' := Metric.mem_closedBall.mp hx
  have hy' := Metric.mem_closedBall.mp hy
  have hlow := dist_triangle4 a x y b
  have hupp := dist_triangle4 x a b y
  rw [dist_comm a x, hab] at hlow
  rw [dist_comm b y, hab] at hupp
  constructor <;> linarith

/-- Every actual smoothed source is carried by the same closed ball, uniformly in its index. -/
theorem radial_smoothed_source_compl_carrier (ν : ProbabilityMeasure Plane) (b : Plane)
    (hν : ∀ᵐ y ∂(ν : Measure Plane), dist y b ≤ 1 / 400) (n : ℕ) :
    (smoothSourceProbability ν (shrinkingRadialBump n) : Measure Plane)
      (Metric.closedBall b (1 / 80))ᶜ = 0 := by
  apply ae_iff.mp
  filter_upwards [ae_dist_le_smoothSourceProbability ν (shrinkingRadialBump n) b hν]
    with y hy
  apply Metric.mem_closedBall.mpr
  linarith [shrinkingRadialBump_rOut_le n]

/-- The original source is carried by the same closed approximation carrier. -/
theorem radial_source_compl_carrier (ν : ProbabilityMeasure Plane) (b : Plane)
    (hν : ∀ᵐ y ∂(ν : Measure Plane), dist y b ≤ 1 / 400) :
    (ν : Measure Plane) (Metric.closedBall b (1 / 80))ᶜ = 0 := by
  apply ae_iff.mp
  filter_upwards [hν] with y hy
  exact Metric.mem_closedBall.mpr (by linarith)

/-- The pointwise smooth source density has the distance bound required by the polar-ray estimate. -/
theorem ae_dist_le_one_of_smooth_density_ne_zero
    (μ ν : ProbabilityMeasure Plane) {a b : Plane} (hab : dist a b = 1 / 4)
    (hμ : ∀ᵐ x ∂(μ : Measure Plane), dist x a ≤ 1 / 400)
    (hν : ∀ᵐ y ∂(ν : Measure Plane), dist y b ≤ 1 / 400) (n : ℕ) :
    ∀ᵐ x ∂(μ : Measure Plane), ∀ y,
      ENNReal.ofReal (smoothMeasureDensity (ν : Measure Plane)
        ((shrinkingRadialBump n).normed volume) y) ≠ 0 → dist x y ≤ 1 := by
  filter_upwards [hμ] with x hx
  intro y hy
  have hreal : smoothMeasureDensity (ν : Measure Plane)
      ((shrinkingRadialBump n).normed volume) y ≠ 0 := by
    intro hz
    exact hy (by rw [hz, ENNReal.ofReal_zero])
  have hsource := dist_le_of_smoothMeasureDensity_normed_ne_zero
    ν (shrinkingRadialBump n) b hν hreal
  have hcarrier : y ∈ Metric.closedBall b (1 / 80) :=
    Metric.mem_closedBall.mpr (by linarith [shrinkingRadialBump_rOut_le n])
  exact (prepared_enlarged_balls_distance_bounds hab (Metric.mem_closedBall.mpr hx) hcarrier).2

end FalconerThetaGauge
