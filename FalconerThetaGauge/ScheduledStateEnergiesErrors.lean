module

public import FalconerThetaGauge.ScheduledStateEnergiesTree

/-! # Actual weighted errors at every visit of the concrete induction tree -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem ProfileChainState.finish_le_terminal_of_valid {s : ProfileChainState} {N δ : ℕ}
    (hs : s.Valid N δ) : s.finish ≤ N := by
  cases s with
  | discrepancy a t => exact hs.2
  | fourier b e a v => exact hs.2.2.1.trans hs.2.2.2.1

theorem regularMeasureExcess_bounds_unit (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N) {n : ℕ} (hn : n ≤ N) :
    -1 ≤ regularMeasureExcess ρ N n ∧ regularMeasureExcess ρ N n ≤ 1 := by
  have h := regularMeasureExcess_lipschitz ρ hρ hN n 0
  simp only [regularMeasureExcess_zero ρ hρ N, sub_zero, Nat.cast_zero,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at h
  have hratio : (n : ℝ) / N ≤ 1 :=
    (div_le_one (by exact_mod_cast hN)).2 (by exact_mod_cast hn)
  obtain ⟨hlo, hhi⟩ := abs_le.1 h
  constructor <;> linarith

theorem regularMeasureProfileBudget_bounds (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N q : ℕ} (hN : 0 < N) (s : ProfileChainState)
    {δ : ℕ} (hs : s.Valid N δ) (hroot : 10 * q ≤ s.finish - s.start) :
    -2 ≤ profileBudget (regularMeasureExcess ρ N) q s.start s.finish ∧
      profileBudget (regularMeasureExcess ρ N) q s.start s.finish ≤ 2 := by
  have hstart := ProfileChainState.start_le_finish_of_valid hs
  have hfinish := ProfileChainState.finish_le_terminal_of_valid hs
  simpa only [mul_one] using
    (profileBudget_bounds (κ := (1 : ℝ)) (by omega) hfinish
      (fun n hn ↦ regularMeasureExcess_bounds_unit ρ hρ hN hn))

/-- The literal `R⁻²⁵` local error, multiplied by the actual path's coefficient. -/
theorem actual_weighted_node_error_le_budget (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain (regularMeasureExcess ρ N)
      (blockCount θ N) N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ (chain.state 0).finish - (chain.state 0).start) :
    chain.multiplierProduct (tolerance θ N) * (2 : ℝ) ^ (-25 * (N : ℝ)) ≤
      (2 : ℝ) ^ (N * (-23 + 24 * blockParameter θ N -
        profileBudget (regularMeasureExcess ρ N) (blockCount θ N)
          (chain.state 0).start (chain.state 0).finish)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hvalid := chain.state_valid (blockCount_pos θ hN)
    (toleranceCount_le_blockCount_of_parameterFacts hpar) (le_refl chain.length)
  have hstart := ProfileChainState.start_le_finish_of_valid hvalid
  have hfinish := ProfileChainState.finish_le_terminal_of_valid hvalid
  have hA := (regularMeasureExcess_bounds_unit ρ hρ hN (hstart.trans hfinish)).2
  have hcost := chain.totalCost_le_excess_final_point ρ hρ hpar hroot (le_refl _) hstart
  calc
    _ ≤ (2 : ℝ) ^ (N * (chain.totalCost + 2 * blockParameter θ N)) *
        (2 : ℝ) ^ (-25 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (chain.multiplierProduct_le_totalCost_add_two_block hpar)
        (by positivity)
    _ = (2 : ℝ) ^ (N * (chain.totalCost + 2 * blockParameter θ N - 25)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N))

/-- Every node visit contributes its own local error, including paths with equal states. -/
def actualProfileTreeError (ρ : Measure Plane) (θ : ℝ) (N : ℕ)
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N)) : ℝ :=
  ((profileInductionVisits (regularMeasureExcess ρ N) θ N s hs).map fun chain ↦
    chain.multiplierProduct (tolerance θ N) * (2 : ℝ) ^ (-25 * (N : ℝ))).sum

theorem actualProfileTreeError_le_profileBudget (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ s.finish - s.start) :
    actualProfileTreeError ρ θ N s hs ≤
      (2 : ℝ) ^ (N * (-23 + 25 * blockParameter θ N -
        profileBudget (regularMeasureExcess ρ N) (blockCount θ N) s.start s.finish)) := by
  let visits := profileInductionVisits (regularMeasureExcess ρ N) θ N s hs
  let C := (2 : ℝ) ^ (N * (-23 + 24 * blockParameter θ N -
    profileBudget (regularMeasureExcess ρ N) (blockCount θ N) s.start s.finish))
  have hbound : ∀ z ∈ visits.map (fun chain ↦
      chain.multiplierProduct (tolerance θ N) * (2 : ℝ) ^ (-25 * (N : ℝ))), z ≤ C := by
    intro z hz
    obtain ⟨chain, hchain, rfl⟩ := Multiset.mem_map.1 hz
    have hstart := profileInductionVisits_initial hs hchain
    have h := actual_weighted_node_error_le_budget ρ hρ hpar chain
      (by simpa only [hstart] using hroot)
    simpa only [hstart] using h
  have hsum := Multiset.sum_le_card_nsmul _ C hbound
  simp only [Multiset.card_map, nsmul_eq_mul] at hsum
  calc
    _ ≤ (visits.card : ℝ) * C := hsum
    _ ≤ (2 : ℝ) ^ (blockParameter θ N * N) * C :=
      mul_le_mul_of_nonneg_right (profileInductionVisits_card_le_block_power hpar hs)
        (by dsimp [C]; positivity)
    _ = _ := by
      dsimp only [C]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- The total genuine weighted error is at most `R⁻²⁰`. -/
theorem actualProfileTreeError_le_small (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (s : ProfileChainState) (hs : s.Valid N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ s.finish - s.start) :
    actualProfileTreeError ρ θ N s hs ≤ (2 : ℝ) ^ (-20 * (N : ℝ)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hbudget := (regularMeasureProfileBudget_bounds ρ hρ hN s hs hroot).1
  have hpar' := hpar
  obtain ⟨_, _, _, _, _, hκhi, hβhi, _, _, _, _, _⟩ := hpar'
  apply (actualProfileTreeError_le_profileBudget ρ hρ hpar s hs hroot).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hκ : blockParameter θ N ≤ 1 / 10000 := hκhi.trans hβhi
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Both actual terminal energies and all local errors fit the literal induction budget. -/
theorem actualProfileTreeTerminalEnergy_add_error_le_budget (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (s : ProfileChainState)
    (hs : s.Valid N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ s.finish - s.start) (initialLevel : ℕ) :
    actualProfileTreeTerminalEnergy ρ θ N s hs initialLevel +
        actualProfileTreeError ρ θ N s hs ≤
      (2 : ℝ) ^ (N * (-profileBudget (regularMeasureExcess ρ N) (blockCount θ N)
        s.start s.finish + 227 * blockParameter θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have hbudget := (regularMeasureProfileBudget_bounds ρ hρ hN s hs hroot).2
  let C := (2 : ℝ) ^ (N * (-profileBudget (regularMeasureExcess ρ N) (blockCount θ N)
    s.start s.finish + 226 * blockParameter θ N))
  have herr : actualProfileTreeError ρ θ N s hs ≤ C := by
    apply (actualProfileTreeError_le_small ρ hρ hpar s hs hroot).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ C + C := add_le_add
      (actualProfileTreeTerminalEnergy_le_budget ρ hρ hpar s hs hroot initialLevel) herr
    _ = 2 * C := by ring
    _ ≤ (2 : ℝ) ^ (blockParameter θ N * N) * C :=
      mul_le_mul_of_nonneg_right
        ((by norm_num : (2 : ℝ) ≤ 2600).trans (parameter_leaf_constant_bound hpar))
        (by dsimp [C]; positivity)
    _ = _ := by
      dsimp only [C]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end FalconerThetaGauge
