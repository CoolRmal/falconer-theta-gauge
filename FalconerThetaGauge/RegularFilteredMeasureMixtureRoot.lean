/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularFilteredMeasureMixtureBounds

/-! # Source 9.3 Steps 1--2 for the single actual finite-piece filtered measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Metric
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def regularRetainedRootSelfEnergy (μ : Measure Plane) (θ : ℝ) (N cutoffK : ℕ)
    (t : RegularRetainedType μ θ N) : ℝ :=
  let ρ := regularRetainedProbability μ θ N t
  let I := regularMeasurePieceTests ρ θ N
  let T := expansionCount θ N
  scheduledFourierEnergySup ρ ρ unitSquare unitSquare (tolerance θ N * N) 2
    (8 * T) I I (2 * T) cutoffK N

theorem regularRetainedRootSelfEnergy_nonneg (μ : Measure Plane) [IsProbabilityMeasure μ]
    (θ : ℝ) (N cutoffK : ℕ) (t : RegularRetainedType μ θ N) :
    0 ≤ regularRetainedRootSelfEnergy μ θ N cutoffK t := by
  let : IsProbabilityMeasure (regularRetainedProbability μ θ N t) :=
    regularRetainedProbability_probability μ θ N t
  exact scheduledFourierEnergySup_nonneg _ _ _ _ _ _ _ _ _ (by omega) _ _

/-- The actual global annulus retains the original mass-weighted self energies. -/
theorem regularFilteredDistanceMeasure_annulus_le_weighted_self_energies
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hballμ : HasGaugeBallBound μ θ C) (hballν : HasGaugeBallBound ν θ C)
    {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1)
    (hSball : S ⊆ ball x₀ (1 / 400)) (hTball : T ⊆ ball y₀ (1 / 400))
    (cutoffK : ℕ) :
    scalarFourierAnnulusIntegral
        (regularFilteredDistanceMeasure μ ν hpar (8 * expansionCount θ N))
        ((N : ℝ) - 1) ((N : ℝ) + 1) ≤
      ∑ p : RegularRetainedType μ θ N × RegularRetainedType ν θ N,
        (regularRetainedPairMass μ ν θ N p).toReal *
          (2 * Real.sqrt (regularRetainedRootSelfEnergy μ θ N cutoffK p.1) *
            Real.sqrt (regularRetainedRootSelfEnergy ν θ N cutoffK p.2) +
              (2 : ℝ) ^ (-(390 * (N : ℝ)))) := by
  have hsep : ∀ x ∈ S, ∀ y ∈ T, (6 / 25 : ℝ) ≤ dist x y := by
    intro x hx y hy
    simpa only [neg_zero, Real.rpow_zero, mul_one, dist_eq_norm] using
      source_pair_distance_lower_root hab (hSball hx) (hTball hy)
  apply (regularFilteredDistanceMeasure_annulus_le_piece_annuli μ ν hpar
    (8 * expansionCount θ N) hS hT hμ hν (by norm_num) hsep
    ((N : ℝ) - 1) ((N : ℝ) + 1)).trans
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have h := preparedRegularParts_mattila_annulus_le_self_energies μ ν hθ hC hballμ hballν
    hpar hconstant p.1.property p.2.property hab hS hT hμ hν hSball hTball 2 cutoffK
  simpa only [regularRetainedPairMeasure, regularRetainedSymbol,
    regularRetainedRootSelfEnergy, regularRetainedProbability] using h

theorem finite_pair_weighted_energy_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι → ℝ) (b g : κ → ℝ) (e : ℝ) :
    (∑ p : ι × κ, a p.1 * b p.2 * (2 * f p.1 * g p.2 + e)) =
      2 * (∑ i, a i * f i) * (∑ j, b j * g j) + e * (∑ i, a i) * (∑ j, b j) := by
  calc
    _ = ∑ p : ι × κ, (2 * ((a p.1 * f p.1) * (b p.2 * g p.2)) +
        e * (a p.1 * b p.2)) := Finset.sum_congr rfl fun p _ ↦ by ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [Fintype.sum_prod_type, ← Finset.sum_mul_sum]
      ring

def regularRetainedRootSqrtEnergyAverage (μ : Measure Plane) (θ : ℝ) (N cutoffK : ℕ) : ℝ :=
  ∑ t : RegularRetainedType μ θ N, (regularRetainedMass μ θ N t).toReal *
    Real.sqrt (regularRetainedRootSelfEnergy μ θ N cutoffK t)

/-- Source Step 2 followed by the true finite mixture: no type-count loss is introduced. -/
theorem regularFilteredDistanceMeasure_annulus_le_sqrt_energy_averages
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hballμ : HasGaugeBallBound μ θ C) (hballν : HasGaugeBallBound ν θ C)
    {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    {x₀ y₀ : Plane} (hab : dist x₀ y₀ = 1 / 4)
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S = 1) (hν : ν T = 1)
    (hSball : S ⊆ ball x₀ (1 / 400)) (hTball : T ⊆ ball y₀ (1 / 400))
    (cutoffK : ℕ) :
    scalarFourierAnnulusIntegral
        (regularFilteredDistanceMeasure μ ν hpar (8 * expansionCount θ N))
        ((N : ℝ) - 1) ((N : ℝ) + 1) ≤
      2 * regularRetainedRootSqrtEnergyAverage μ θ N cutoffK *
        regularRetainedRootSqrtEnergyAverage ν θ N cutoffK +
          (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  have h := regularFilteredDistanceMeasure_annulus_le_weighted_self_energies μ ν hθ hC
    hballμ hballν hpar hconstant hab hS hT hμ hν hSball hTball cutoffK
  simp only [regularRetainedPairMass, ENNReal.toReal_mul] at h
  rw [finite_pair_weighted_energy_sum
    (fun i ↦ (regularRetainedMass μ θ N i).toReal)
    (fun i ↦ Real.sqrt (regularRetainedRootSelfEnergy μ θ N cutoffK i))
    (fun j ↦ (regularRetainedMass ν θ N j).toReal)
    (fun j ↦ Real.sqrt (regularRetainedRootSelfEnergy ν θ N cutoffK j))] at h
  apply h.trans
  have hmμ := sum_regularRetainedMass_toReal_le_one μ θ N
  have hmν := sum_regularRetainedMass_toReal_le_one ν θ N
  have hm : (∑ i, (regularRetainedMass μ θ N i).toReal) *
      (∑ j, (regularRetainedMass ν θ N j).toReal) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hmμ hmν
      (Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg) (by norm_num : (0 : ℝ) ≤ 1)
  have he := mul_le_mul_of_nonneg_left hm
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(390 * (N : ℝ))))
  simpa only [regularRetainedRootSqrtEnergyAverage, mul_assoc, mul_one] using
    add_le_add (le_refl (2 * regularRetainedRootSqrtEnergyAverage μ θ N cutoffK *
      regularRetainedRootSqrtEnergyAverage ν θ N cutoffK)) he

end FalconerThetaGauge
