module

public import FalconerThetaGauge.DirectionalTestsAverageShells

/-! # True pair-ball mass bounds from the regular normalized-anchor probability -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The actual pair-distance mass is bounded by a uniform bound on the source's actual balls. -/
theorem real_dyadicPairBall_le_of_closedBall (ν : Measure Plane) [IsProbabilityMeasure ν]
    (d : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hball : ∀ z, ν.real (Metric.closedBall z (dyadicRadius d)) ≤ B) :
    (ν.prod ν).real (dyadicPairBall d) ≤ B := by
  have heq (z : Plane) : (Prod.mk z ⁻¹' dyadicPairBall d) =
      Metric.closedBall z (dyadicRadius d) := by
    ext z'
    simp only [mem_preimage, dyadicPairBall, mem_ofPred_eq, Metric.mem_closedBall,
      dist_eq_norm, norm_sub_rev]
  have hmass : (ν.prod ν) (dyadicPairBall d) ≤ ENNReal.ofReal B := by
    rw [Measure.prod_apply (measurableSet_dyadicPairBall d)]
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal B ∂ν := by
        apply lintegral_mono
        intro z
        change ν (Prod.mk z ⁻¹' dyadicPairBall d) ≤ ENNReal.ofReal B
        rw [heq]
        have h := ENNReal.ofReal_le_ofReal (hball z)
        simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top ν _)] using h
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal hB hmass

/-- The actual normalized-anchor pair mass in the source excess notation. -/
theorem real_projectionAnchor_dyadicPairBall_le_excess (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {ε : ℝ} {N p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hp : p ≤ N) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) (d : ℕ) :
    ((projectionAnchorMeasure ρ p P).prod (projectionAnchorMeasure ρ p P)).real
      (dyadicPairBall d) ≤
      9 * (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ (-((d : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N d)) := by
  have := isProbabilityMeasure_projectionAnchorMeasure ρ p P hP
  apply real_dyadicPairBall_le_of_closedBall _ d (by positivity)
  intro z
  exact real_projectionAnchor_closedBall_le_excess ρ hρ hN hreg hp P hP d z

/-- Interval height controls each actual intermediate-depth excess difference. -/
theorem regularMeasureExcess_sub_le_profileHeight (ρ : Measure Plane) (N p u : ℕ)
    {d : ℕ} (hdp : p ≤ d) (hdu : d ≤ u) :
    regularMeasureExcess ρ N p - regularMeasureExcess ρ N d ≤
      profileHeight (regularMeasureExcess ρ N) p p u := by
  unfold profileHeight
  exact sub_le_sub_left (profileMinimum_le hdp hdu) _

/-- The genuine normalized pair mass is controlled by the actual interval height. -/
theorem real_projectionAnchor_dyadicPairBall_le_height (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {ε : ℝ} {N p u : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hp : p ≤ N) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) {d : ℕ} (hdp : p ≤ d) (hdu : d ≤ u) :
    ((projectionAnchorMeasure ρ p P).prod (projectionAnchorMeasure ρ p P)).real
      (dyadicPairBall d) ≤
      9 * (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ (-((d : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * profileHeight (regularMeasureExcess ρ N) p p u) := by
  apply (real_projectionAnchor_dyadicPairBall_le_excess ρ hρ hN hreg hp P hP d).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_left
    (regularMeasureExcess_sub_le_profileHeight ρ N p u hdp hdu) (Nat.cast_nonneg N)

end FalconerThetaGauge
