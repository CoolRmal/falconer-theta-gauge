module

public import FalconerThetaGauge.SpaceSplittingBudgetTerminal

/-! # The literal stationary error has the source R⁻⁴⁰⁰ decay -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_stationary_sqrt_le_three {phase : ℝ} (hphase : 1 ≤ phase) :
    Real.sqrt (2 * Real.pi / phase) ≤ 3 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · rw [div_le_iff₀ (by linarith : 0 < phase)]
    nlinarith [Real.pi_lt_four]

theorem spaceSplitting_stationary_remainder_le {θ : ℝ} {N L : ℕ}
    (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest)
    (hcard : I.card ≤ N ^ 2 + 1) (hL : L ≤ N) {h v r d : ℝ}
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ v - h)
    (hr : (2 : ℝ) ^ v / 4 ≤ r) (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    Real.sqrt (2 * Real.pi / (r * d)) *
        circularStationaryRemainderBase (expansionCount θ N)
          (2 * max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) *
        (circularStationaryRemainderBase (expansionCount θ N)
          (2 * max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) /
          (r * d)) ^ expansionCount θ N ≤ (2 : ℝ) ^ (-400 * (N : ℝ)) := by
  let T := expansionCount θ N
  let B := circularStationaryRemainderBase T
    (2 * max 1 (scheduledSymbolScale T (tolerance θ N * N) I L))
  have hphase : 1 ≤ r * d := spaceSplitting_phase_scale_ge_one hpar.2.2.1.1
    ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
      hgap) hr hd
  have hB₀ : 0 ≤ B := by dsimp [B, circularStationaryRemainderBase]; positivity
  have hq₀ : 0 ≤ B / (r * d) := div_nonneg hB₀ (by linarith)
  have hq := spaceSplitting_remainder_ratio_le hpar I hcard hgap hr hd
  have hpow := (pow_le_pow_left₀ hq₀ hq T).trans (spaceSplitting_decay_ratio_pow_le hpar)
  have hB := spaceSplitting_remainderBase_le_terminal hpar I hcard hL
  have hs := spaceSplitting_stationary_sqrt_le_three hphase
  have hN : (2 : ℝ) ≤ N := by
    have hn : (4 : ℝ) ≤ N := by exact_mod_cast hpar.1
    linarith
  have hthree : (3 : ℝ) ≤ (2 : ℝ) ^ (N : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hN
  change Real.sqrt (2 * Real.pi / (r * d)) * B * (B / (r * d)) ^ T ≤ _
  calc
    _ ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (3 * (N : ℝ)) *
        (2 : ℝ) ^ (-450 * (N : ℝ)) := mul_le_mul
      (mul_le_mul (hs.trans hthree) hB hB₀ (by positivity)) hpow
      (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (-446 * (N : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

end FalconerThetaGauge
