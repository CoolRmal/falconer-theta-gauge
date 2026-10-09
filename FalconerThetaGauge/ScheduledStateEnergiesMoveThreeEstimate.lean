module

public import FalconerThetaGauge.ScheduledStateEnergiesOrthogonality
public import FalconerThetaGauge.ScheduledStateEnergiesMoveThreeFacts

/-! # The full analytic Move 3 at an actual longest remaining scheduled test -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

set_option maxHeartbeats 800000 in
theorem regularMeasureStateEnergy_moveThree (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (b e a v : ℕ)
    (hs : (ProfileChainState.fourier b e a v).Valid N (toleranceCount θ N))
    (hlong : 100 * blockCount θ N < v - a) (test : ProfileScheduleTest)
    (htest : test ∈ profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a)
    (hlargest : test.length =
      profileLongestTestLength (regularMeasureExcess ρ N) (blockCount θ N) N b e a)
    (hlarge : v - a ≤ 2 * test.length) :
    regularMeasureStateEnergy ρ θ N i (.fourier b e a v) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) test.anchor a test.anchor +
        12 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N i (.fourier b e test.anchor v) +
      (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hq := blockCount_pos θ hN
  have hδq := toleranceCount_le_blockCount_of_parameterFacts hpar
  have hgeo := profileRemainingTests_refinement_real_geometry hq hδq hs hlong htest
    hlarge (tolerance_mul_scale θ hN)
  have hL : ∀ s ∈ profileRemainingTests (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a, s.length ≤ test.length := by
    intro s hs'
    exact (profileRemainingTests_length_le_longest hs').trans_eq hlargest.symm
  have hh := profileFourierStateEnergy_le_orthogonality ρ hρ hpar hreg hs.2.2.2.1
    hgeo.1 hgeo.2.1 (hs.2.2.1.trans hs.2.2.2.1) hgeo.2.2.1
    hgeo.2.2.2.1 hgeo.2.2.2.2.1 hgeo.2.2.2.2.2.1 i hi
    (profileRemainingTests_refinement_tube hq hs.2.2.2.1 htest) hL hgeo.2.2.2.2.2.2
  have hc := profileHeight_refinement_le_parent (A := regularMeasureExcess ρ N)
    hgeo.1 hgeo.2.1
  have hm := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_left (add_le_add hc (le_refl (12 * tolerance θ N)))
      (Nat.cast_nonneg N))
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_right hm
      (regularMeasureStateEnergy_nonneg ρ θ N i (.fourier b e test.anchor v))) le_rfl)

theorem regularMeasureStateEnergy_moveThree_le_uniform_error (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (b e a v : ℕ)
    (hs : (ProfileChainState.fourier b e a v).Valid N (toleranceCount θ N))
    (hlong : 100 * blockCount θ N < v - a) (test : ProfileScheduleTest)
    (htest : test ∈ profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a)
    (hlargest : test.length =
      profileLongestTestLength (regularMeasureExcess ρ N) (blockCount θ N) N b e a)
    (hlarge : v - a ≤ 2 * test.length) :
    regularMeasureStateEnergy ρ θ N i (.fourier b e a v) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) test.anchor a test.anchor +
        12 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N i (.fourier b e test.anchor v) +
      (2 : ℝ) ^ (-(25 * (N : ℝ))) := by
  have hh := regularMeasureStateEnergy_moveThree ρ hρ hpar hreg i hi b e a v hs hlong
    test htest hlargest hlarge
  exact hh.trans (add_le_add le_rfl
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)))

end FalconerThetaGauge
