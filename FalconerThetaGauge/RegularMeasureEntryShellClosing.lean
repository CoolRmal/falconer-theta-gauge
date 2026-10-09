/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryOrthogonalityParts

/-! # Exact closing of source 9.3 after the actual entry-state estimate -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Metric
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def entryShellSelfEnergyBound (θ : ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ ((N : ℝ) * (-gain θ N + 301 * blockParameter θ N +
    12 * tolerance θ N + 2 / N)) + (2 : ℝ) ^ (-80 * (N : ℝ))

theorem entryShellSelfEnergyBound_nonneg (θ : ℝ) (N : ℕ) :
    0 ≤ entryShellSelfEnergyBound θ N := by
  unfold entryShellSelfEnergyBound
  positivity

/-- The actual entry budget and entry jump close once the true state estimate is supplied. -/
theorem regularRetainedRootSelfEnergy_le_shell_bound_of_entry_state_bound
    (μ : Measure Plane) [IsProbabilityMeasure μ] {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hball : HasGaugeBallBound μ θ C) {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    (t : RegularRetainedType μ θ N)
    (hstate : let ρ := regularRetainedProbability μ θ N t
      let c := regularMeasureEntryDepth ρ θ N
      regularMeasureStateEnergy ρ θ N 0 (.fourier c N c N) ≤
        (2 : ℝ) ^ (N * (-2 * gain θ N + 300 * blockParameter θ N + 2 / N))) :
    regularRetainedRootSelfEnergy μ θ N (8 * expansionCount θ N) t ≤
      entryShellSelfEnergyBound θ N := by
  have hroot := regularRetainedRootSelfEnergy_le_entry_state μ hθ hC hball hpar hconstant t
  apply hroot.trans
  unfold entryShellSelfEnergyBound
  rw [show -(80 * (N : ℝ)) = (-80 : ℝ) * N by ring]
  apply add_le_add _ le_rfl
  calc
    _ ≤ (2 : ℝ) ^ (N * (gain θ N + blockParameter θ N + 12 * tolerance θ N)) *
        (2 : ℝ) ^ (N * (-2 * gain θ N + 300 * blockParameter θ N + 2 / N)) :=
      mul_le_mul_of_nonneg_left hstate (by positivity)
    _ = (2 : ℝ) ^ ((N : ℝ) * (-gain θ N + 301 * blockParameter θ N +
        12 * tolerance θ N + 2 / N)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem regularRetainedRootSqrtEnergyAverage_le_sqrt (μ : Measure Plane)
    [IsProbabilityMeasure μ] (θ : ℝ) (N cutoffK : ℕ) {B : ℝ}
    (_hB : 0 ≤ B) (hself : ∀ t : RegularRetainedType μ θ N,
      regularRetainedRootSelfEnergy μ θ N cutoffK t ≤ B) :
    regularRetainedRootSqrtEnergyAverage μ θ N cutoffK ≤ Real.sqrt B := by
  calc
    _ ≤ ∑ t : RegularRetainedType μ θ N,
        (regularRetainedMass μ θ N t).toReal * Real.sqrt B := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hself t)) ENNReal.toReal_nonneg
    _ = (∑ t : RegularRetainedType μ θ N, (regularRetainedMass μ θ N t).toReal) *
        Real.sqrt B := by rw [Finset.sum_mul]
    _ ≤ 1 * Real.sqrt B := mul_le_mul_of_nonneg_right
      (sum_regularRetainedMass_toReal_le_one μ θ N) (Real.sqrt_nonneg B)
    _ = Real.sqrt B := one_mul _

/-- The only remaining analytic input is the actual entry-state decay for each retained part. -/
theorem regularFilteredDistanceMeasure_shell_bound_of_entry_state_bounds
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hballμ : HasGaugeBallBound μ θ C) (hballν : HasGaugeBallBound ν θ C)
    {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1)
    (hSball : S ⊆ ball x₀ (1 / 400)) (hTball : T ⊆ ball y₀ (1 / 400))
    (hstateμ : ∀ t : RegularRetainedType μ θ N,
      let ρ := regularRetainedProbability μ θ N t
      let c := regularMeasureEntryDepth ρ θ N
      regularMeasureStateEnergy ρ θ N 0 (.fourier c N c N) ≤
        (2 : ℝ) ^ (N * (-2 * gain θ N + 300 * blockParameter θ N + 2 / N)))
    (hstateν : ∀ t : RegularRetainedType ν θ N,
      let ρ := regularRetainedProbability ν θ N t
      let c := regularMeasureEntryDepth ρ θ N
      regularMeasureStateEnergy ρ θ N 0 (.fourier c N c N) ≤
        (2 : ℝ) ^ (N * (-2 * gain θ N + 300 * blockParameter θ N + 2 / N))) :
    scalarFourierAnnulusIntegral
        (regularFilteredDistanceMeasure μ ν hpar (8 * expansionCount θ N))
        ((N : ℝ) - 1) ((N : ℝ) + 1) ≤ (2 : ℝ) ^ (-gain θ N * N / 3) := by
  let B := entryShellSelfEnergyBound θ N
  have hB : 0 ≤ B := entryShellSelfEnergyBound_nonneg θ N
  have hselfμ := fun t ↦ regularRetainedRootSelfEnergy_le_shell_bound_of_entry_state_bound μ
    hθ hC hballμ hpar hconstant t (hstateμ t)
  have hselfν := fun t ↦ regularRetainedRootSelfEnergy_le_shell_bound_of_entry_state_bound ν
    hθ hC hballν hpar hconstant t (hstateν t)
  have hμavg := regularRetainedRootSqrtEnergyAverage_le_sqrt μ θ N
    (8 * expansionCount θ N) hB hselfμ
  have hνavg := regularRetainedRootSqrtEnergyAverage_le_sqrt ν θ N
    (8 * expansionCount θ N) hB hselfν
  have hνavg0 : 0 ≤ regularRetainedRootSqrtEnergyAverage ν θ N
      (8 * expansionCount θ N) := Finset.sum_nonneg fun _ _ ↦ by positivity
  have havgs := mul_le_mul hμavg hνavg hνavg0 (Real.sqrt_nonneg B)
  rw [Real.mul_self_sqrt hB] at havgs
  have hroot := regularFilteredDistanceMeasure_annulus_le_sqrt_energy_averages μ ν hθ hC
    hballμ hballν hpar hconstant hab hS hT hμ hν hSball hTball (8 * expansionCount θ N)
  have herr : (2 : ℝ) ^ (-(390 * (N : ℝ))) ≤ (2 : ℝ) ^ (-30 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hmid : scalarFourierAnnulusIntegral
      (regularFilteredDistanceMeasure μ ν hpar (8 * expansionCount θ N))
      ((N : ℝ) - 1) ((N : ℝ) + 1) ≤ 2 * B + (2 : ℝ) ^ (-30 * (N : ℝ)) := by
    apply hroot.trans
    simpa only [mul_assoc] using add_le_add
      (mul_le_mul_of_nonneg_left havgs (by norm_num : (0 : ℝ) ≤ 2)) herr
  exact hmid.trans (parameter_shell_numeric_bound hpar)

end FalconerThetaGauge
