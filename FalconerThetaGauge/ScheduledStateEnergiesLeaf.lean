module

public import FalconerThetaGauge.ScheduledStateEnergiesShort
public import FalconerThetaGauge.RegularMeasureEntryChainMultipliers

/-! # Actual weighted terminal energies are paid by the concrete chain's profile budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- This terminal contribution uses the actual measure energy, not an abstract leaf bound. -/
theorem actual_weighted_short_leaf_le_budget (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain (regularMeasureExcess ρ N)
      (blockCount θ N) N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ (chain.state 0).finish - (chain.state 0).start)
    (hshort : (chain.state chain.length).finish - (chain.state chain.length).start ≤
      100 * blockCount θ N) (i : ℕ) :
    chain.multiplierProduct (tolerance θ N) *
        regularMeasureStateEnergy ρ θ N i (chain.state chain.length) ≤
      (2 : ℝ) ^ (N * (-profileBudget (regularMeasureExcess ρ N) (blockCount θ N)
        (chain.state 0).start (chain.state 0).finish + 225 * blockParameter θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hvalid := chain.state_valid (blockCount_pos θ hN)
    (toleranceCount_le_blockCount_of_parameterFacts hpar) (le_refl chain.length)
  have hcost := chain.totalCost_le_excess_final_point ρ hρ hpar hroot
    (le_refl (chain.state chain.length).start)
    (ProfileChainState.start_le_finish_of_valid hvalid)
  calc
    _ ≤ (2 : ℝ) ^ (N * (chain.totalCost + 2 * blockParameter θ N)) *
        (2 : ℝ) ^ (N * (-2 * regularMeasureExcess ρ N (chain.state chain.length).start +
          201 * blockParameter θ N)) :=
      mul_le_mul (chain.multiplierProduct_le_totalCost_add_two_block hpar)
        (regularMeasureStateEnergy_short_le_parameterBudget ρ hρ hpar i _ hvalid hshort)
        (regularMeasureStateEnergy_nonneg ρ θ N i _) (by positivity)
    _ = (2 : ℝ) ^ (N * (chain.totalCost -
        2 * regularMeasureExcess ρ N (chain.state chain.length).start +
          203 * blockParameter θ N)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)

end FalconerThetaGauge
