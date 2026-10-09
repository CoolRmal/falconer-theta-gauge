module

public import FalconerThetaGauge.ScheduledStateEnergiesReached
public import FalconerThetaGauge.RegularMeasureEntryChainBudget

/-! # Genuine terminal-state bounds from the literal integral estimates and rounded parameters -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem ProfileChainState.start_le_finish_of_valid {s : ProfileChainState} {N δ : ℕ}
    (hs : s.Valid N δ) : s.start ≤ s.finish := by
  cases s with
  | discrepancy a t => exact hs.1
  | fourier b e a v => exact hs.2.1

theorem regularMeasureStateEnergy_le_uniform (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) (θ : ℝ) {N : ℕ} (hN : 0 < N) (i : ℕ)
    (s : ProfileChainState) {δ : ℕ} (hs : s.Valid N δ) :
    regularMeasureStateEnergy ρ θ N i s ≤
      2600 * (4 : ℝ) ^ ((s.finish : ℝ) - s.start) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N s.start) := by
  cases s with
  | discrepancy a t =>
    have hdiff : 0 ≤ (t : ℝ) - a := sub_nonneg.2 (by exact_mod_cast hs.1)
    apply (regularMeasureStateEnergy_discrepancy_le_excess ρ hρ θ hN i a t).trans
    change _ ≤ 2600 * (4 : ℝ) ^ ((t : ℝ) - a) * _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      (2 : ℝ) ^ ((t : ℝ) - a) ≤ (4 : ℝ) ^ ((t : ℝ) - a) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) hdiff
      _ ≤ _ := by nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) ((t : ℝ) - a)]
  | fourier b e a v =>
    exact regularMeasureStateEnergy_fourier_le_excess ρ hρ θ hN i b e a v

theorem regularMeasureStateEnergy_short_le_integerBudget (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) (θ : ℝ) {N : ℕ} (hN : 0 < N)
    (i : ℕ) (s : ProfileChainState) {δ q : ℕ} (hs : s.Valid N δ)
    (hshort : s.finish - s.start ≤ 100 * q) :
    regularMeasureStateEnergy ρ θ N i s ≤
      2600 * (2 : ℝ) ^ (200 * (q : ℝ)) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N s.start) := by
  have hdiff : (s.finish : ℝ) - s.start ≤ 100 * (q : ℝ) := by
    have h := Nat.cast_le (α := ℝ).2 hshort
    rwa [Nat.cast_sub (ProfileChainState.start_le_finish_of_valid hs), Nat.cast_mul,
      Nat.cast_ofNat] at h
  apply (regularMeasureStateEnergy_le_uniform ρ hρ θ hN i s hs).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (4 : ℝ) ^ ((s.finish : ℝ) - s.start) =
        (2 : ℝ) ^ (2 * ((s.finish : ℝ) - s.start)) := by
      rw [Real.rpow_mul (by norm_num)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Short actual states have the source's terminal excess bound with an explicit `201κ` loss. -/
theorem regularMeasureStateEnergy_short_le_parameterBudget (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (i : ℕ) (s : ProfileChainState)
    (hs : s.Valid N (toleranceCount θ N))
    (hshort : s.finish - s.start ≤ 100 * blockCount θ N) :
    regularMeasureStateEnergy ρ θ N i s ≤
      (2 : ℝ) ^ (N * (-2 * regularMeasureExcess ρ N s.start + 201 * blockParameter θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hεN : (16 : ℝ) ≤ tolerance θ N * N := hpar.2.2.1.1
  rw [tolerance_mul_scale θ hN] at hεN
  have hδ : 16 ≤ toleranceCount θ N := by exact_mod_cast hεN
  have hq : 16 ≤ blockCount θ N :=
    hδ.trans (toleranceCount_le_blockCount_of_parameterFacts hpar)
  have hc : (2600 : ℝ) ≤ (2 : ℝ) ^ (blockCount θ N : ℝ) := by
    rw [Real.rpow_natCast]
    exact (by norm_num : (2600 : ℝ) ≤ 2 ^ (16 : ℕ)).trans
      (pow_le_pow_right₀ (by norm_num) hq)
  calc
    _ ≤ 2600 * (2 : ℝ) ^ (200 * (blockCount θ N : ℝ)) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N s.start) :=
      regularMeasureStateEnergy_short_le_integerBudget ρ hρ θ hN i s hs hshort
    _ ≤ (2 : ℝ) ^ (blockCount θ N : ℝ) * (2 : ℝ) ^ (200 * (blockCount θ N : ℝ)) *
        (2 : ℝ) ^ (-2 * N * regularMeasureExcess ρ N s.start) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      have heq := blockParameter_mul_scale θ hN
      nlinarith

end FalconerThetaGauge
