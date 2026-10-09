/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureShellSummability
public import FalconerThetaGauge.FilteredDistanceMeasureApproximation

/-! # Actual weighted-measure reconstruction after the remaining space recurrence -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

/-- The concrete `8T` filters satisfy all reconstruction hypotheses once Move 4 is supplied. -/
theorem weightedCrossDistanceMeasure_absolutelyContinuous_of_space_split
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ C K : ℝ} (hθ : 2 / 3 < θ) (hC : 0 < C) (hK : 0 ≤ K)
    (hballμ : HasGaugeBallBound μ θ C) (hballν : HasGaugeBallBound ν θ C)
    (hunitμ : μ unitSquare = 1) (hunitν : ν unitSquare = 1)
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1)
    (hSball : S ⊆ ball x₀ (1 / 400)) (hTball : T ⊆ ball y₀ (1 / 400))
    (hpinμ : ∀ x ∈ S,
      circleArcLength.withDensity (radialProjectionDensity ν x) = ν.map (radialProjection x) ∧
      radialOrliczMoment ν 8 x ≤ ENNReal.ofReal K)
    (hpinν : ∀ y ∈ T,
      circleArcLength.withDensity (radialProjectionDensity μ y) = μ.map (radialProjection y) ∧
      radialOrliczMoment μ 8 y ≤ ENNReal.ofReal K)
    (N₀ : ℕ) (hpar : ∀ N, N₀ ≤ N → ParameterFacts θ N)
    (hconstant : ∀ N, N₀ ≤ N → Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    (hspaceμ : ∀ N, N₀ ≤ N → ∀ t : RegularRetainedType μ θ N,
      ActualSpaceSplittingRecurrence (regularRetainedProbability μ θ N t) θ N)
    (hspaceν : ∀ N, N₀ ≤ N → ∀ t : RegularRetainedType ν θ N,
      ActualSpaceSplittingRecurrence (regularRetainedProbability ν θ N t) θ N) :
    weightedCrossDistanceMeasure μ ν ≪ volume := by
  let M := N₀ + 1
  let F₁ : ∀ n : ℕ, FiniteDirectionalFilter (n + M)
      (tolerance θ (n + M) * ((n + M : ℕ) : ℝ)) := fun n ↦
    regularDirectionalFilter μ (hpar (n + M) (by omega)) (8 * expansionCount θ (n + M))
  let F₂ : ∀ n : ℕ, FiniteDirectionalFilter (n + M)
      (tolerance θ (n + M) * ((n + M : ℕ) : ℝ)) := fun n ↦
    regularDirectionalFilter ν (hpar (n + M) (by omega)) (8 * expansionCount θ (n + M))
  let τ := finiteTestFilteredDistanceSequence μ ν θ M F₁ F₂
  have hsep : ∀ x ∈ S, ∀ y ∈ T, (24 / 100 : ℝ) ≤ dist x y := by
    intro x hx y hy
    have h := source_pair_distance_lower_root hab (hSball hx) (hTball hy)
    norm_num only [neg_zero, Real.rpow_zero, mul_one] at h
    rw [show (24 / 100 : ℝ) = 6 / 25 by norm_num]
    simpa only [dist_eq_norm] using h
  have happrox := finiteTestFilteredDistanceSequence_summable_removed_mass μ ν hθ hK M
    (fun n ↦ hpar (n + M) (by omega)) hunitμ hunitν hS hT hμ hν hsep F₁ F₂
    (fun n ↦ regularDirectionalFilter_carrier μ _ _)
    (fun n ↦ regularDirectionalFilter_carrier ν _ _) hpinμ hpinν
  let : IsFiniteMeasure (weightedCrossDistanceMeasure μ ν) := happrox.1
  let : ∀ n, IsFiniteMeasure (τ n) := happrox.2.1
  apply absolutelyContinuous_of_summable_dyadic_reconstruction
    (weightedCrossDistanceMeasure μ ν) τ N₀ happrox.2.2.1 happrox.2.2.2
  have henergy (n : ℕ) : dyadicMeasureFourierEnergy (τ n) (n + N₀ + 1) ≤
      (2 : ℝ) ^ (-gain θ (n + M) * ((n + M : ℕ) : ℝ) / 3) := by
    rw [show n + N₀ + 1 = n + M by omega,
      dyadicMeasureFourierEnergy_eq_scalarFourierAnnulusIntegral]
    have hh := regularFilteredDistanceMeasure_shell_bound_of_space_split μ ν (by linarith) hC
      hballμ hballν (hpar (n + M) (by omega)) (hconstant (n + M) (by omega))
      hab hS hT hμ hν hSball hTball (hspaceμ (n + M) (by omega))
      (hspaceν (n + M) (by omega))
    exact hh
  have hs : Summable (fun N : ℕ ↦ (2 : ℝ) ^ (-gain θ N * N / 3)) := by
    convert summable_dyadic_gain_power θ (1 / 3) (by linarith) (by norm_num) using 1
    ext N
    congr 1
    ring
  exact Summable.of_nonneg_of_le
    (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) henergy ((summable_nat_add_iff M).2 hs)

end FalconerThetaGauge
