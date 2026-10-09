/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaCellsEstimate
public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwo
public import FalconerThetaGauge.ScheduledStateEnergiesReached

/-! # The literal high-shell Mattila step on actual scheduled profile state energies -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

set_option maxHeartbeats 800000 in
theorem profileMaskedDistanceHighShellEnergy_le_fourier_state
    (ρ : Measure Plane) [IsProbabilityMeasure ρ] (A : ℕ → ℝ)
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (i a t : ℕ) (ht : t ≤ N) (hlong : 100 * blockCount θ N < t - a)
    (cutoffK v : ℕ) (hvlo : t - toleranceCount θ N < v) (hvhi : v ≤ t) :
    profileMaskedDistanceHighShellEnergy ρ A (blockCount θ N) N (tolerance θ N * N)
        (maskLevelCount θ N) i (8 * expansionCount θ N) a t v ≤
      2 * profileFourierStateEnergy ρ A (blockCount θ N) N (tolerance θ N * N)
        (maskLevelCount θ N) i (8 * expansionCount θ N) (2 * expansionCount θ N)
        cutoffK a t a v + (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  let E := tolerance θ N * N
  let T := expansionCount θ N
  let q := blockCount θ N
  let δ := toleranceCount θ N
  let I := profileScheduledTests A q N a t
  let F := profileFourierStateEnergy ρ A q N E (maskLevelCount θ N) i
    (8 * T) (2 * T) cutoffK a t a v
  have hN : 0 < N := by have := hpar.1; omega
  have hq : 0 < q := blockCount_pos θ hN
  have hδq : δ ≤ q := toleranceCount_le_blockCount_of_parameterFacts hpar
  have hδ : E = (δ : ℝ) := tolerance_mul_scale θ hN
  have hwNat : 10 * δ + a ≤ v := by omega
  have hw : 10 * E ≤ (v : ℝ) - a := by
    rw [hδ]
    have h : (10 : ℝ) * δ + a ≤ v := by exact_mod_cast hwNat
    linarith
  have hlenNat : 2 * ((t - a) / 2) + a ≤ v + δ := by omega
  have hlength : 2 * (((t - a) / 2 : ℕ) : ℝ) ≤ (v : ℝ) - a + E := by
    rw [hδ]
    have h : (2 : ℝ) * (((t - a) / 2 : ℕ) : ℝ) + a ≤ (v : ℝ) + δ := by
      exact_mod_cast hlenNat
    linarith
  have hL : ∀ test ∈ I, test.length ≤ (t - a) / 2 := by
    intro test htest
    have hs := profileScheduledTests_length_bounds hq ht htest
    omega
  have hc : I.card ≤ N ^ 2 + 1 :=
    (profileScheduledTests_card_le_scale_sq A hpar ht).trans (by omega)
  have hLN : (t - a) / 2 ≤ N := by omega
  have hF : 0 ≤ F := profileFourierStateEnergy_nonneg ..
  unfold profileMaskedDistanceHighShellEnergy
  apply finiteEnergyMaximum_le _ _ (add_nonneg (mul_nonneg (by norm_num) hF)
    (by positivity))
  intro pair hpair
  obtain ⟨hpair, hsep⟩ := Finset.mem_filter.mp hpair
  obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hpair
  have hcell := levelMaskedDistance_mattila_cells_estimate hpar ρ ρ hsep hP hQ
    (maskLevelCount θ N) i I I hL hL hc hc hLN hLN cutoffK v (hvhi.trans ht)
    hw hlength hlength
  have hdrop := scheduledFourierEnergySup_drop_reached ρ ρ E
    (directionalLevelWidth (maskLevelCount θ N) i) (8 * T) I I
    (k₀ := 2 * T) (by omega) a hP hQ cutoffK v
  have hstate := scheduledFourierEnergySup_remaining_le_refined_state ρ A q N E
    (maskLevelCount θ N) i (8 * T) (k₀ := 2 * T) (by omega)
    cutoffK a t (a := a) (p := a) (le_refl a) v hP hQ
  have hsup : scheduledFourierEnergySup ρ ρ (dyadicCube a pair.1) (dyadicCube a pair.2)
      E (directionalLevelWidth (maskLevelCount θ N) i) (8 * T) I I (2 * T) cutoffK v ≤ F :=
    hdrop.trans hstate
  exact hcell.trans (add_le_add
    (mul_le_mul_of_nonneg_left hsup (by norm_num)) le_rfl)

end FalconerThetaGauge
