module

public import FalconerThetaGauge.ScheduledStateEnergiesLowHigh

/-! # Literal rounded low-frequency child and finite high-frequency children of Move 2 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

theorem scalarHighDyadicIndices_nat (s t : ℕ) :
    scalarHighDyadicIndices (s : ℝ) t = Finset.Ioc s t := by
  ext v
  simp only [scalarHighDyadicIndices, Finset.mem_filter, Finset.mem_range, Nat.cast_lt,
    Finset.mem_Ioc]
  omega

/-- The source's low/high step acts on genuine state energies and its actual finite shell list. -/
theorem regularMeasureStateEnergy_low_high (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (i a t : ℕ) (ht : t ≤ N) (hfreq : a < t - toleranceCount θ N) :
    regularMeasureStateEnergy ρ θ N i (.discrepancy a t) ≤
      320 * regularMeasureStateEnergy ρ θ N (i + 1)
        (.discrepancy a (t - toleranceCount θ N)) +
      320 * ∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
        profileMaskedDistanceHighShellEnergy ρ (regularMeasureExcess ρ N) (blockCount θ N) N
          (tolerance θ N * N) (maskLevelCount θ N) i (8 * expansionCount θ N) a t v := by
  have hN : 0 < N := by have := hpar.1; omega
  have hsize : (maskLevelCount θ N : ℝ) ≤ (2 : ℝ) ^ (toleranceCount θ N : ℝ) / 8 := by
    rw [← tolerance_mul_scale θ hN]
    exact hpar.directional_level_size
  have hlevels : 0 < maskLevelCount θ N := by unfold maskLevelCount; omega
  have h := profileDistanceStateEnergy_low_high ρ hρ (regularMeasureExcess ρ N)
    (blockCount_pos θ hN) hlevels hsize i (8 * expansionCount θ N) a t ht hfreq
  rw [scalarHighDyadicIndices_nat, ← tolerance_mul_scale θ hN] at h
  exact h

theorem regularMeasureHighShells_card_le_toleranceCount (θ : ℝ) (N t : ℕ) :
    (Finset.Ioc (t - toleranceCount θ N) t).card ≤ toleranceCount θ N := by
  rw [Nat.card_Ioc]
  omega

end FalconerThetaGauge
