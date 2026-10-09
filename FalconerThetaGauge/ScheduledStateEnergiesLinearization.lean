module

public import FalconerThetaGauge.DistanceLinearizationEstimate
public import FalconerThetaGauge.ScheduledStateEnergiesBounds

/-! # The actual right-split branch of the discrepancy induction -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem profileScheduledTests_right_split_projection {A : ℕ → ℝ} {q N a t : ℕ}
    (hlong : 100 * q < t - a)
    (hright : a + t < 2 * profileSplitPoint A q N a t) :
    (⟨.projection, profileSplitPoint A q N a t, t⟩ : ProfileScheduleTest) ∈
      profileScheduledTests A q N a t := by
  apply mem_biUnion.mpr
  refine ⟨(a, t), mem_profileScheduleOrigins_iff.mpr
    ⟨le_refl a, by omega, by omega, le_refl t, hlong⟩, ?_⟩
  unfold profileContributedTests profileTestsAtSplit
  apply Finset.mem_union_right
  simp only [hright, ite_true, Finset.mem_singleton]

/-- Every shorter child test has the exact anchor and length needed in Estimate 7.7. -/
theorem profileScheduledTests_short_at_finish {A : ℕ → ℝ} {q N a p : ℕ}
    (hq : 0 < q) (hp : p ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profileScheduledTests A q N a p) :
    test.anchor ≤ p ∧ a + test.length ≤ p := by
  have hb := profileScheduledTests_length_bounds hq hp htest
  omega

/-- Estimate 7.7 applied to the literal finite cell maximum and constructed child list. -/
theorem profileDistanceStateEnergy_le_linearization (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N q a t : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    (hright : a + t < 2 * profileSplitPoint (regularMeasureExcess ρ N) q N a t)
    {L i : ℕ} (hL : 0 < L) (hi : i + 1 ≤ L)
    (hsize : (L : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8) :
    profileDistanceStateEnergy ρ (regularMeasureExcess ρ N) q N
        (tolerance θ N * N) L i a t ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
        (profileSplitPoint (regularMeasureExcess ρ N) q N a t)
        (profileSplitPoint (regularMeasureExcess ρ N) q N a t) t + 7 * tolerance θ N)) *
        profileDistanceStateEnergy ρ (regularMeasureExcess ρ N) q N
          (tolerance θ N * N) L (i + 1) a
          (profileSplitPoint (regularMeasureExcess ρ N) q N a t) := by
  let A := regularMeasureExcess ρ N
  let p := profileSplitPoint A q N a t
  have hp := profileSplitPoint_bounds (A := A) hq ht hlong
  have hpN : p ≤ N := by dsimp only [p]; omega
  have hordered := profileScheduledTests_ordered A hq hpN (a := a)
  have hshort : ∀ test ∈ profileScheduledTests A q N a p,
      test.anchor ≤ p ∧ a + test.length ≤ p :=
    fun _ htest ↦ profileScheduledTests_short_at_finish hq hpN htest
  have hsubset := profileScheduledTests_mono A q N (le_refl a) (show p ≤ t by omega)
  unfold profileDistanceStateEnergy
  apply finiteEnergyMaximum_le _ _
    (mul_nonneg (by positivity) (profileDistanceStateEnergy_nonneg ..))
  intro P hP
  obtain ⟨hPQ, hsep⟩ := mem_filter.mp hP
  obtain ⟨hP, hQ⟩ := mem_product.mp hPQ
  apply (scheduledDistanceEnergy_level_le_linearization ρ hρ hpar hreg
    (show a ≤ p by omega) hsep (show p < t by omega) ht hright hL hi hsize
    (profileScheduledTests_right_split_projection hlong hright) hsubset hsubset
    hordered hordered hshort hshort).trans
  exact mul_le_mul_of_nonneg_left
    (scheduledDistanceEnergy_le_profileDistanceStateEnergy ρ A q N
      (tolerance θ N * N) L (i + 1) a p hP hQ hsep) (by positivity)

/-- Move 1 for genuine analytic state values, with its actual scheduled masks. -/
theorem regularMeasureStateEnergy_moveOne (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (a t : ℕ) (ht : t ≤ N)
    (hlong : 100 * blockCount θ N < t - a)
    (hright : a + t <
      2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) :
    regularMeasureStateEnergy ρ θ N i (.discrepancy a t) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) t +
          7 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N (i + 1)
          (.discrepancy a
            (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t)) := by
  have hN : 0 < N := by have := hpar.1; omega
  exact profileDistanceStateEnergy_le_linearization ρ hρ hpar hreg (blockCount_pos θ hN)
    ht hlong hright (by unfold maskLevelCount; omega) hi hpar.directional_level_size

end FalconerThetaGauge
