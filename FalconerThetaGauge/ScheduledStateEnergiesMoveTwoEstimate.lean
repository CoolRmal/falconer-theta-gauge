module

public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwoBudget
public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwoMattila

/-! # The full analytic Move 2 for genuine discrepancy and Fourier state energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

set_option maxHeartbeats 800000 in
theorem regularMeasureStateEnergy_moveTwo_raw (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (a t : ℕ) (ht : t ≤ N)
    (hlong : 100 * blockCount θ N < t - a)
    (hleft : 2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t ≤ a + t) :
    regularMeasureStateEnergy ρ θ N i (.discrepancy a t) ≤
      320 * regularMeasureStateEnergy ρ θ N (i + 1)
        (.discrepancy a (t - toleranceCount θ N)) +
      640 * (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) a
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) +
        12 * tolerance θ N)) *
        (∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
          regularMeasureStateEnergy ρ θ N i (.fourier a t
            (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) v)) +
      640 * (toleranceCount θ N : ℝ) * (2 : ℝ) ^ (-(80 * (N : ℝ))) +
      320 * (toleranceCount θ N : ℝ) * (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  let D := (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
    (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) a
    (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) +
      12 * tolerance θ N))
  let F := fun v ↦ regularMeasureStateEnergy ρ θ N i (.fourier a t
    (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) v)
  let J := Finset.Ioc (t - toleranceCount θ N) t
  have hs : (∑ v ∈ J, regularMeasureStateEnergy ρ θ N i (.fourier a t a v)) ≤
      D * (∑ v ∈ J, F v) + (toleranceCount θ N : ℝ) *
        (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
    have hh : (∑ v ∈ J, regularMeasureStateEnergy ρ θ N i (.fourier a t a v)) ≤
        ∑ v ∈ J, (D * F v + (2 : ℝ) ^ (-(80 * (N : ℝ)))) := by
      apply sum_le_sum
      intro v hv
      obtain ⟨hvlo, hvhi⟩ := mem_Ioc.mp hv
      exact regularMeasureStateEnergy_moveTwo_orthogonality ρ hρ hpar hreg
        i hi a t ht hlong hleft v hvlo hvhi
    have hc : (J.card : ℝ) ≤ toleranceCount θ N := by
      exact_mod_cast regularMeasureHighShells_card_le_toleranceCount θ N t
    simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hh
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (by positivity)))
  have h := regularMeasureStateEnergy_moveTwo_mattila ρ hρ hpar i a t ht hlong
  have hh := h.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num))) le_rfl)
  convert hh using 1
  dsimp only [D, F, J]
  ring

set_option maxHeartbeats 800000 in
theorem regularMeasureStateEnergy_moveTwo (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N) (a t : ℕ) (ht : t ≤ N)
    (hlong : 100 * blockCount θ N < t - a)
    (hleft : 2 * profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t ≤ a + t) :
    regularMeasureStateEnergy ρ θ N i (.discrepancy a t) ≤
      320 * regularMeasureStateEnergy ρ θ N (i + 1)
        (.discrepancy a (t - toleranceCount θ N)) +
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N)
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) a
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) +
        13 * tolerance θ N)) *
        (∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
          regularMeasureStateEnergy ρ θ N i (.fourier a t
            (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) v)) +
      (2 : ℝ) ^ (-(25 * (N : ℝ))) := by
  have h := regularMeasureStateEnergy_moveTwo_raw ρ hρ hpar hreg i hi a t ht hlong hleft
  have hmult := moveTwo_high_multiplier_le hpar
    (profileHeight (regularMeasureExcess ρ N)
      (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) a
      (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t))
  have hsum : 0 ≤ ∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
      regularMeasureStateEnergy ρ θ N i (.fourier a t
        (profileSplitPoint (regularMeasureExcess ρ N) (blockCount θ N) N a t) v) :=
    sum_nonneg fun _ _ ↦ regularMeasureStateEnergy_nonneg ..
  have hh := mul_le_mul_of_nonneg_right hmult hsum
  have he := moveTwo_high_shell_error_le hpar
  linarith

end FalconerThetaGauge
