module

public import FalconerThetaGauge.ScheduledStateEnergiesOrthogonality

/-! # Orthogonality at the genuine left split for every actual high shell of Move 2 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

set_option maxHeartbeats 800000 in
theorem regularMeasureStateEnergy_moveTwo_orthogonality (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (a t : ℕ) (ht : t ≤ N)
    (hlong : 100 * blockCount θ N < t - a)
    (hleft : 2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t ≤ a + t)
    (v : ℕ) (hvlo : t - toleranceCount θ N < v) (hvhi : v ≤ t) :
    regularMeasureStateEnergy ρ θ N i (.fourier a t a v) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) a
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) +
        12 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N i
          (.fourier a t (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) v) +
      (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
  let A := regularMeasureExcess ρ N
  let q := blockCount θ N
  let δ := toleranceCount θ N
  let p := profileSplitPoint A q N a t
  have hN : 0 < N := by have := hpar.1; omega
  have hq : 0 < q := blockCount_pos θ hN
  have hδq : δ ≤ q := toleranceCount_le_blockCount_of_parameterFacts hpar
  have hδ : tolerance θ N * N = (δ : ℝ) := tolerance_mul_scale θ hN
  have hleft' : 2 * p ≤ a + t := hleft
  have hgeo := profileSplitPoint_left_shell_geometry (A := A) (q := q) (δ := δ)
    hq ht hlong hδq hleft' hvlo
  have hap : a ≤ p := hgeo.1
  have hpv : p ≤ v := hgeo.2.1
  have hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p := by
    rw [hδ]
    have hh : 10 * (δ : ℝ) + p ≤ v := by exact_mod_cast hgeo.2.2.1
    linarith
  have hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N) := by
    rw [hδ]
    have hn : p + p ≤ a + v + 2 * δ := by omega
    have hh : (p : ℝ) + p ≤ a + v + 2 * δ := by exact_mod_cast hn
    linarith
  have hlength : (((t - a) / 2 : ℕ) : ℝ) ≤
      (v : ℝ) - p + 2 * (tolerance θ N * N) := by
    rw [hδ]
    have hn : (t - a) / 2 + p ≤ v + 2 * δ := by omega
    have hh : (((t - a) / 2 : ℕ) : ℝ) + p ≤ v + 2 * δ := by exact_mod_cast hn
    linarith
  have hI := profileRemainingTests_at_base A hq ht (a := a)
  have htest : (⟨.tube, p, a⟩ : ProfileScheduleTest) ∈
      profileRemainingTests A q N a t a := by
    rw [hI]
    exact profileScheduledTests_left_split_tube hq ht hlong hleft
  have hL : ∀ test ∈ profileRemainingTests A q N a t a, test.length ≤ (t - a) / 2 := by
    intro test htest
    rw [hI] at htest
    have := profileScheduledTests_length_bounds hq ht htest
    omega
  exact profileFourierStateEnergy_le_orthogonality ρ hρ hpar hreg ht (le_refl a)
    hap (hvhi.trans ht) hpv (by
      simp only [sub_self]
      have := tolerance_pos θ hN
      positivity)
    hw hgap i hi htest hL hlength

end FalconerThetaGauge
