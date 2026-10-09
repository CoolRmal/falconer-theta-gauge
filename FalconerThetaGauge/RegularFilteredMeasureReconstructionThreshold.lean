/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureReconstruction

/-! # The finite starting scale is chosen from the actual parameters and gauge constant -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem exists_parameter_constant_threshold (θ : ℝ) (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1)
    (C : ℝ) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      ParameterFacts θ N ∧ Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2 := by
  obtain ⟨Npar, hpar⟩ := exists_parameter_threshold θ hθ₀ hθ₁
  have ht := (tendsto_gain_mul_scale_atTop θ (by linarith)).const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 2000)
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually_ge_atTop (Real.log C / Real.log 2))
  refine ⟨max (max Npar M) 1, ?_⟩
  intro N hN
  have hNpar : Npar ≤ N := (le_max_left Npar M).trans ((le_max_left _ _).trans hN)
  have hNM : M ≤ N := (le_max_right Npar M).trans ((le_max_left _ _).trans hN)
  have hNpos : 0 < N := by have := (le_max_right (max Npar M) 1).trans hN; omega
  refine ⟨hpar N hNpar, (hM N hNM).trans ?_⟩
  have hk := mul_le_mul_of_nonneg_right (gain_div_le_blockParameter θ hNpos)
    (Nat.cast_nonneg (α := ℝ) N)
  nlinarith

/-- An initial tail is chosen internally; the remaining hypothesis is exactly actual Move 4. -/
theorem weightedCrossDistanceMeasure_absolutelyContinuous_of_space_split_all_scales
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ C K : ℝ} (hθ₀ : 2 / 3 < θ) (hθ₁ : θ < 1) (hC : 0 < C) (hK : 0 ≤ K)
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
    (hspaceμ : ∀ N, ParameterFacts θ N → ∀ t : RegularRetainedType μ θ N,
      ActualSpaceSplittingRecurrence (regularRetainedProbability μ θ N t) θ N)
    (hspaceν : ∀ N, ParameterFacts θ N → ∀ t : RegularRetainedType ν θ N,
      ActualSpaceSplittingRecurrence (regularRetainedProbability ν θ N t) θ N) :
    weightedCrossDistanceMeasure μ ν ≪ volume := by
  obtain ⟨N₀, hN₀⟩ := exists_parameter_constant_threshold θ hθ₀ hθ₁ C
  exact weightedCrossDistanceMeasure_absolutelyContinuous_of_space_split μ ν hθ₀ hC hK
    hballμ hballν hunitμ hunitν hab hS hT hμ hν hSball hTball hpinμ hpinν N₀
    (fun N hN ↦ (hN₀ N hN).1) (fun N hN ↦ (hN₀ N hN).2)
    (fun N hN ↦ hspaceμ N (hN₀ N hN).1) (fun N hN ↦ hspaceν N (hN₀ N hN).1)

end FalconerThetaGauge
