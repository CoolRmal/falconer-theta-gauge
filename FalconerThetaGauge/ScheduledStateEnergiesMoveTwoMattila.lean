/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.ScheduledStateEnergiesMattila

/-! # The genuine Move 2 low/high step after the full Mattila shell estimate -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeSeparatedMeasures

set_option maxHeartbeats 800000 in
theorem regularMeasureStateEnergy_moveTwo_mattila (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (i a t : ℕ) (ht : t ≤ N)
    (hlong : 100 * blockCount θ N < t - a) :
    regularMeasureStateEnergy ρ θ N i (.discrepancy a t) ≤
      320 * regularMeasureStateEnergy ρ θ N (i + 1)
        (.discrepancy a (t - toleranceCount θ N)) +
      640 * ∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
        regularMeasureStateEnergy ρ θ N i (.fourier a t a v) +
      320 * (toleranceCount θ N : ℝ) * (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  have hδq := toleranceCount_le_blockCount_of_parameterFacts hpar
  have hfreq : a < t - toleranceCount θ N := by omega
  have hlow := regularMeasureStateEnergy_low_high ρ hρ hpar i a t ht hfreq
  have hsum : (∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
      profileMaskedDistanceHighShellEnergy ρ (regularMeasureExcess ρ N) (blockCount θ N) N
        (tolerance θ N * N) (maskLevelCount θ N) i (8 * expansionCount θ N) a t v) ≤
      ∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
        (2 * regularMeasureStateEnergy ρ θ N i (.fourier a t a v) +
          (2 : ℝ) ^ (-(390 * (N : ℝ)))) := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨hvlo, hvhi⟩ := Finset.mem_Ioc.mp hv
    exact profileMaskedDistanceHighShellEnergy_le_fourier_state
      ρ (regularMeasureExcess ρ N) hpar i a t ht hlong (8 * expansionCount θ N)
      v hvlo hvhi
  have hc : ((Finset.Ioc (t - toleranceCount θ N) t).card : ℝ) ≤ toleranceCount θ N := by
    exact_mod_cast regularMeasureHighShells_card_le_toleranceCount θ N t
  calc
    _ ≤ 320 * regularMeasureStateEnergy ρ θ N (i + 1)
        (.discrepancy a (t - toleranceCount θ N)) +
        320 * ∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
          (2 * regularMeasureStateEnergy ρ θ N i (.fourier a t a v) +
            (2 : ℝ) ^ (-(390 * (N : ℝ)))) :=
      hlow.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by norm_num)))
    _ = 320 * regularMeasureStateEnergy ρ θ N (i + 1)
        (.discrepancy a (t - toleranceCount θ N)) +
        640 * ∑ v ∈ Finset.Ioc (t - toleranceCount θ N) t,
          regularMeasureStateEnergy ρ θ N i (.fourier a t a v) +
        320 * ((Finset.Ioc (t - toleranceCount θ N) t).card : ℝ) *
          (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr

end FalconerThetaGauge
