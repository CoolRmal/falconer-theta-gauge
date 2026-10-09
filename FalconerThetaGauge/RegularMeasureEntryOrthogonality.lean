/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryOrthogonalityCells

/-! # The actual orthogonality jump from the root to the constructed entry depth -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem ParameterFacts.mattila_entry_gap {θ : ℝ} {N c : ℕ}
    (hpar : ParameterFacts θ N) (hc : (c : ℝ) < (N : ℝ) / 4) :
    10 * (tolerance θ N * N) ≤ (N : ℝ) - c := by
  have hN : 0 < N := by have := hpar.1; omega
  have hk := blockParameter_pos θ hN
  rcases hpar.2.2.2.2 with ⟨_, hkg, hgsmall, _, he, _, _, _⟩
  have hκone : blockParameter θ N ≤ 1 := by linarith
  have hκsq : blockParameter θ N ^ 2 ≤ 1 := by nlinarith
  have hε : tolerance θ N ≤ 1 / 500000 := by linarith
  have hεN := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) N)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem rootPieceFourierEnergy_le_entry_state (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hc : (regularMeasureEntryDepth ρ θ N : ℝ) < (N : ℝ) / 4) :
    let c := regularMeasureEntryDepth ρ θ N
    scheduledFourierEnergySup ρ ρ unitSquare unitSquare (tolerance θ N * N) 2
        (8 * expansionCount θ N) (regularMeasurePieceTests ρ θ N)
        (regularMeasurePieceTests ρ θ N) (2 * expansionCount θ N)
        (8 * expansionCount θ N) N ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) c 0 c +
        12 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N 0 (.fourier c N c N) +
          (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
  let c := regularMeasureEntryDepth ρ θ N
  let E := tolerance θ N * N
  let T := expansionCount θ N
  let I := regularMeasurePieceTests ρ θ N
  let levels := maskLevelCount θ N
  have hN : 0 < N := by have := hpar.1; omega
  have hq := blockCount_pos θ hN
  have hε := tolerance_pos θ hN
  have hcle : c ≤ N := by
    have hreal : (c : ℝ) ≤ N := by linarith
    exact_mod_cast hreal
  have hhalf : 2 * c ≤ N := by
    have hreal : (2 : ℝ) * c ≤ N := by linarith
    exact_mod_cast hreal
  have hlevels : 0 < levels := by unfold levels maskLevelCount; omega
  have hwidth : 1 ≤ directionalLevelWidth levels (0 + 1) :=
    directionalLevelWidth_ge_one hlevels (by unfold levels maskLevelCount; omega)
  have hw : 10 * E ≤ (N : ℝ) - c := hpar.mattila_entry_gap hc
  have hgap : (c : ℝ) - (0 : ℝ) ≤ (N : ℝ) - c + 2 * E := by
    have hh : (2 : ℝ) * c ≤ N := by exact_mod_cast hhalf
    have hE : 0 ≤ E := mul_nonneg hε.le (Nat.cast_nonneg N)
    linarith
  have htest : (⟨.tube, c, 0⟩ : ProfileScheduleTest) ∈ I :=
    mem_union_left _ (mem_singleton_self _)
  have hL : ∀ test ∈ I, test.length ≤ N - c := by
    intro test ht
    exact (profilePieceTests_root_lengths hq hhalf ht).2
  have hlength : ((N - c : ℕ) : ℝ) ≤ (N : ℝ) - c + 2 * E := by
    rw [Nat.cast_sub hcle]
    have hE : 0 ≤ E := mul_nonneg hε.le (Nat.cast_nonneg N)
    linarith
  apply csSup_le (scheduledFourierEnergyValues_nonempty ..)
  rintro z ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  have hb₁' : b₁ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels 0)
      (8 * T) I (2 * T) := by
    simpa only [directionalLevelWidth, Nat.cast_zero, zero_div, sub_zero] using hb₁
  have hb₂' : b₂ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels 0)
      (8 * T) I (2 * T) := by
    simpa only [directionalLevelWidth, Nat.cast_zero, zero_div, sub_zero] using hb₂
  have h := maskedFourierEnergy_le_orthogonality ρ hρ (a := 0) (g := 0)
    (p := c) (v := N) hpar hreg (le_refl 0) (Nat.zero_le c) (le_refl N) hcle
    (by simp only [Nat.cast_zero, sub_zero]; positivity) hw
    (by simpa only [Nat.cast_zero] using hgap) hlevels
    hpar.directional_level_size 0 hwidth (regularMeasurePieceTests_ordered ρ hpar) htest
    (profilePieceTests_card_le_scale_sq_add_one _ hpar) hL hlength hb₁' hb₂'
    (zero_mem_occupiedUnitCells ρ hρ) (zero_mem_occupiedUnitCells ρ hρ)
  rw [dyadicCube_zero_eq_unitSquare] at h
  have hs := sum_maskedFourierEnergy_piece_le_entry_state ρ hρ hpar 0 hb₁' hb₂'
  rw [dyadicCube_zero_eq_unitSquare] at hs
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hs (by positivity)) le_rfl)

end FalconerThetaGauge
