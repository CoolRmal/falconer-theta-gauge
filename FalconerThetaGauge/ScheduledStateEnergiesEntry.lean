module

public import FalconerThetaGauge.ScheduledStateEnergiesSpaceRecurrence
public import FalconerThetaGauge.RegularFilteredMeasureMixtureRoot

/-! # Actual retained entry states after the remaining space-splitting recurrence -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- The true entry budget turns the actual tree estimate into the retained-state decay. -/
theorem regularRetainedEntryStateEnergy_le_of_space_split (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hball : HasGaugeBallBound μ θ C) {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    (t : RegularRetainedType μ θ N)
    (hspace : ActualSpaceSplittingRecurrence (regularRetainedProbability μ θ N t) θ N) :
    let ρ := regularRetainedProbability μ θ N t
    let c := regularMeasureEntryDepth ρ θ N
    regularMeasureStateEnergy ρ θ N 0 (.fourier c N c N) ≤
      (2 : ℝ) ^ (N * (-2 * gain θ N + 227 * blockParameter θ N + 2 / N)) := by
  let ρ := regularRetainedProbability μ θ N t
  let c := regularMeasureEntryDepth ρ θ N
  have hp := regularDyadicPartMeasure_probability μ (tolerance θ N) (blockParameter θ N)
    N t.property
  let : IsProbabilityMeasure ρ := hp.1
  have he := regularDyadicPart_entry_properties μ hθ hC hball hpar hconstant t.property
  have hc : c ≤ N := by
    have hh : (c : ℝ) < (N : ℝ) / 4 := he.2.1
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (c : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hvalid : (ProfileChainState.fourier c N c N).Valid N (toleranceCount θ N) :=
    ⟨le_refl c, hc, le_refl N, le_refl N, by omega⟩
  have hroot : 10 * blockCount θ N ≤ N - c := by
    have hh : 100 * blockCount θ N < N - c := he.2.2.1
    omega
  have hreg := regularDyadicPartMeasure_isRegularThrough μ hpar.2.2.1.1 t.val
  have ht := regularMeasureStateEnergy_tree_budget_of_space_split ρ hp.2 hpar hreg hspace
    (.fourier c N c N) hvalid hroot (initial := 0) (by omega)
  apply ht.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hb : 2 * gain θ N - 2 / (N : ℝ) ≤
      profileBudget (regularMeasureExcess ρ N) (blockCount θ N) c N := he.2.2.2.2.1
  exact mul_le_mul_of_nonneg_left (by
    change -profileBudget (regularMeasureExcess ρ N) (blockCount θ N) c N +
      227 * blockParameter θ N ≤ _
    linarith) (Nat.cast_nonneg N)

/-- The literal manuscript's coarser `300κ` bound follows from the sharper actual tree budget. -/
theorem regularRetainedEntryStateEnergy_le_source_of_space_split (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hball : HasGaugeBallBound μ θ C) {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    (t : RegularRetainedType μ θ N)
    (hspace : ActualSpaceSplittingRecurrence (regularRetainedProbability μ θ N t) θ N) :
    let ρ := regularRetainedProbability μ θ N t
    let c := regularMeasureEntryDepth ρ θ N
    regularMeasureStateEnergy ρ θ N 0 (.fourier c N c N) ≤
      (2 : ℝ) ^ (N * (-2 * gain θ N + 300 * blockParameter θ N + 2 / N)) := by
  apply (regularRetainedEntryStateEnergy_le_of_space_split μ hθ hC hball hpar hconstant
    t hspace).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := (blockParameter_pos θ hN).le
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)

end FalconerThetaGauge
