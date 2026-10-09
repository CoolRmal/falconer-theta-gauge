/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.ScheduledStateEnergiesSpaceFacts

/-! # The actual space-splitting depth supplies every literal source margin -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

theorem profileLongestTestLength_le_terminal {A : ℕ → ℝ} {q N b e a : ℕ}
    (hq : 0 < q) (he : e ≤ N) : profileLongestTestLength A q N b e a ≤ N := by
  unfold profileLongestTestLength
  apply Finset.sup_le
  intro test htest
  have hb := profileScheduledTests_length_bounds hq he (mem_filter.mp htest).1
  omega

theorem toleranceCount_ge_sixteen_of_parameterFacts {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) : 16 ≤ toleranceCount θ N := by
  have hN : 0 < N := by have := hpar.1; omega
  have hh := hpar.2.2.1.1
  rw [tolerance_mul_scale θ hN] at hh
  exact_mod_cast hh

theorem regularRemainingTests_card_le {ρ : Measure Plane} {θ : ℝ} {N b e a : ℕ}
    (hpar : ParameterFacts θ N) (he : e ≤ N) :
    (profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a).card ≤
      N ^ 2 + 1 := by
  exact (Finset.card_le_card (filter_subset _ _)).trans
    ((profileScheduledTests_card_le_scale_sq (regularMeasureExcess ρ N) hpar he).trans
      (by omega))

/-- The true near depth has the stationary margin and leaves the whole depth sum below `v`. -/
theorem regularProfileNearStart_source_geometry {ρ : Measure Plane} {θ : ℝ}
    {N b e a v : ℕ} (hpar : ParameterFacts θ N)
    (hs : (ProfileChainState.fourier b e a v).Valid N (toleranceCount θ N))
    (hlong : 100 * blockCount θ N < v - a)
    (hsmall : 2 * profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a < v - a) :
    let p := profileNearStart (regularMeasureExcess ρ N) (blockCount θ N) N
      (toleranceCount θ N) b e a v
    a < p ∧ p ≤ v ∧ p ≤ N ∧ p + 12 ≤ v + 1 ∧
      min (v + 1) (p + 12) = p + 12 ∧
      2 * max (profileLongestTestLength (regularMeasureExcess ρ N)
        (blockCount θ N) N b e a : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - p := by
  dsimp only
  let p := profileNearStart (regularMeasureExcess ρ N) (blockCount θ N) N
    (toleranceCount θ N) b e a v
  have hg := profileNearStart_strict_geometry
    (A := regularMeasureExcess ρ N) (toleranceCount_le_blockCount_of_parameterFacts hpar)
    hlong hsmall
  have hδ := toleranceCount_ge_sixteen_of_parameterFacts hpar
  have hN : 0 < N := by have := hpar.1; omega
  have hpv : p ≤ v := hg.2.1
  have hgap : p + 2 * max (profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a) (toleranceCount θ N) = v := by
    have := hg.2.2
    change v - p = _ at this
    omega
  have h12 : p + 12 ≤ v + 1 := by
    have := le_max_right (profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a) (toleranceCount θ N)
    omega
  have hreal : (p : ℝ) + 2 * max (profileLongestTestLength (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a : ℝ) (toleranceCount θ N : ℝ) = v := by
    exact_mod_cast hgap
  have hvN : v ≤ N := hs.2.2.1.trans hs.2.2.2.1
  refine ⟨hg.1, hpv, hpv.trans hvN, h12, min_eq_right h12, ?_⟩
  rw [tolerance_mul_scale θ hN]
  linarith

end FalconerThetaGauge
