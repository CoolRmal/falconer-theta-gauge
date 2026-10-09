/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaAnnulusEstimate
public import FalconerThetaGauge.MaskedMattilaGeometry

/-! # The full-annulus Mattila estimate for the actual prepared root pair -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem pairDirection_mem_arc_of_prepared_balls {x₀ y₀ x y : Plane}
    (hab : dist x₀ y₀ = 1 / 4) (hx : x ∈ ball x₀ (1 / 400))
    (hy : y ∈ ball y₀ (1 / 400)) :
    pairDirection x y ∈ closedDirectionArc (radialAngle y₀ x₀) (1 / 40) := by
  have habne : x₀ ≠ y₀ := dist_pos.mp (by rw [hab]; norm_num)
  have hxy : x ≠ y := dist_pos.mp (by
    have h := (prepared_balls_distance_bounds hab hx hy).1
    linarith)
  apply pairDirection_mem_arc_of_relative_displacement habne hxy
  have hx' := mem_ball.mp hx
  have hy' := mem_ball.mp hy
  rw [dist_eq_norm] at hx' hy'
  rw [show (x - y) - (x₀ - y₀) = (x - x₀) - (y - y₀) by abel, hab]
  have hn := norm_sub_le (x - x₀) (y - y₀)
  linarith

theorem ParameterFacts.mattila_root_gap {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    10 * (tolerance θ N * N) ≤ (N : ℝ) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hk := blockParameter_pos θ hN
  rcases hpar.2.2.2.2 with ⟨_, hkg, hgsmall, _, he, _, _, _⟩
  have hκone : blockParameter θ N ≤ 1 := by linarith
  have hκsq : blockParameter θ N ^ 2 ≤ 1 := by nlinarith
  have hε : tolerance θ N ≤ 1 / 500000 := by linarith
  have hεN := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) N)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem restrict_eq_self_of_probability_mass_one (μ : Measure Plane)
    [IsProbabilityMeasure μ] {S : Set Plane} (hS : MeasurableSet S) (hμ : μ S = 1) :
    μ.restrict S = μ := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_mem_iff_measure_eq hS.nullMeasurableSet).mpr (by simpa using hμ)

set_option maxHeartbeats 800000 in
theorem preparedRoot_mattila_annulus_estimate {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S₁ S₂ : Set Plane} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hρ₁ : ρ₁ S₁ = 1) (hρ₂ : ρ₂ S₂ = 1)
    (hS₁ball : S₁ ⊆ ball x₀ (1 / 400)) (hS₂ball : S₂ ⊆ ball y₀ (1 / 400))
    (width : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hlength₁ : ∀ test ∈ I₁, 2 * test.length ≤ N)
    (hlength₂ : ∀ test ∈ I₂, 2 * test.length ≤ N) (cutoffK : ℕ) :
    scalarFourierAnnulusIntegral
        (filteredCrossDistanceMeasure ρ₁ ρ₂ (directionalPairMask
          (ScheduledSymbolData.maskProduct.symbol ρ₁ (tolerance θ N * N) width
            (8 * expansionCount θ N) I₁)
          (ScheduledSymbolData.maskProduct.symbol ρ₂ (tolerance θ N * N) width
            (8 * expansionCount θ N) I₂))) ((N : ℝ) - 1) ((N : ℝ) + 1) ≤
      2 * scheduledFourierEnergySup ρ₁ ρ₂ S₁ S₂ (tolerance θ N * N) width
        (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK N +
      (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  have hm₁ : ρ₁.real S₁ = 1 := by simp [Measure.real, hρ₁]
  have hm₂ : ρ₂.real S₂ = 1 := by simp [Measure.real, hρ₂]
  have hL₁ : ∀ test ∈ I₁, test.length ≤ N / 2 := by
    intro test ht
    have := hlength₁ test ht
    omega
  have hL₂ : ∀ test ∈ I₂, test.length ≤ N / 2 := by
    intro test ht
    have := hlength₂ test ht
    omega
  have hlen : 2 * ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) - (0 : ℝ) + tolerance θ N * N := by
    have h : 2 * (N / 2 : ℕ) ≤ N := by omega
    have h' : (2 : ℝ) * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast h
    linarith [hpar.2.2.1.1]
  have hballs := source_spatial_separated_balls_root hab
  have hi := builtMaskedDistance_mattila_annulus_estimate hpar ρ₁ ρ₂
    hballs.1 hballs.2 hS₁ hS₂ (by rw [hm₁, hm₂]; norm_num)
    (hS₁ball.trans ball_subset_closedBall) (hS₂ball.trans ball_subset_closedBall)
    width (radialAngle y₀ x₀) 0 I₁ I₂ hL₁ hL₂ hc₁ hc₂
    (by omega) (by omega) cutoffK N (le_refl N)
    (source_spatial_inverse_coefficient_root hab)
    (fun _x hx _y hy ↦ pairDirection_mem_arc_of_prepared_balls hab (hS₁ball hx) (hS₂ball hy))
    (by simpa only [sub_zero] using hpar.mattila_root_gap) hlen hlen
    (fun r hr x hx y hy ↦ by
      have hd : (6 / 25 : ℝ) * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) ≤ dist x y := by
        simpa only [Nat.cast_zero, dist_eq_norm] using
          source_pair_distance_lower_root hab (hS₁ball hx) (hS₂ball hy)
      simpa only [Nat.cast_zero] using source_frequency_distance_lower hr hd)
    (fun x hx y hy ↦ by
      apply source_pair_distance_terminal_lower (a := 0) (Nat.zero_le N)
      simpa only [Nat.cast_zero, dist_eq_norm] using
        source_pair_distance_lower_root hab (hS₁ball hx) (hS₂ball hy))
  simpa only [builtMaskedDistanceMeasure,
    restrict_eq_self_of_probability_mass_one ρ₁ hS₁ hρ₁,
    restrict_eq_self_of_probability_mass_one ρ₂ hS₂ hρ₂,
    hm₁, hm₂, one_mul, div_one] using hi

end FalconerThetaGauge
