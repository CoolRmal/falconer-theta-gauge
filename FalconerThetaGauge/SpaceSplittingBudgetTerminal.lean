module

public import FalconerThetaGauge.SpaceSplittingBudget
public import FalconerThetaGauge.StationaryCircularInversionTerminal

/-! # The genuine far-term stationary remainder is uniformly at most R⁻⁴⁰⁰ -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_phase_scale_ge_one {E h v r d : ℝ} (hE : 16 ≤ E)
    (hgap : 2 * E ≤ v - h) (hr : (2 : ℝ) ^ v / 4 ≤ r)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) : 1 ≤ r * d := by
  have hh := mul_le_mul hr hd (by positivity : 0 ≤ (5 / 4 : ℝ) * 2 ^ (-h))
    (lt_of_lt_of_le (by positivity : 0 < (2 : ℝ) ^ v / 4) hr).le
  have hp : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ (v - h) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hl : (5 / 16 : ℝ) * (2 : ℝ) ^ (v - h) ≤ r * d := by
    convert hh using 1
    rw [show (2 : ℝ) ^ v / 4 * ((5 / 4 : ℝ) * (2 : ℝ) ^ (-h)) =
      (5 / 16 : ℝ) * ((2 : ℝ) ^ v * (2 : ℝ) ^ (-h)) by ring,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp only [sub_eq_add_neg]
  norm_num at hp
  linarith

theorem spaceSplitting_remainderBase_le_terminal {θ : ℝ} {N L : ℕ}
    (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest)
    (hcard : I.card ≤ N ^ 2 + 1) (hL : L ≤ N) :
    circularStationaryRemainderBase (expansionCount θ N)
        (2 * max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) ≤
      (2 : ℝ) ^ (3 * (N : ℝ)) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let M := max 1 (scheduledSymbolScale T E I L)
  have hN : 0 < N := by have := hpar.1; omega
  have hT : 1 ≤ T := Nat.ceil_pos.mpr (by have := tolerance_pos θ hN; positivity)
  have hE : E ≤ N := by
    dsimp [E]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (parameterFacts_tolerance_le_one hpar) (Nat.cast_nonneg N)
  have hF : 1 ≤ (2 : ℝ) ^ (N : ℝ) := Real.one_le_rpow (by norm_num) (Nat.cast_nonneg _)
  have hfactor : max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) ≤ (2 : ℝ) ^ (N : ℝ) := by
    apply max_le hF
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have hl : (L : ℝ) ≤ N := by exact_mod_cast hL
          have he := hpar.2.2.1.1; change 16 ≤ E at he; linarith)
  have hM := scheduledSymbolScale_max_one_le hT N E I L hcard hF hfactor
  have hs := pow_le_pow_left₀
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) hM 2
  change circularStationaryRemainderBase T (2 * M) ≤ _
  rw [spaceSplitting_remainderBase_eq]
  calc
    _ ≤ 400000000 * ((T : ℝ) + 1) ^ 4 *
        (128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (400000000 * 16384 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
        ((N : ℝ) ^ 2 + 1) ^ 2) * (2 : ℝ) ^ (2 * (N : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    _ ≤ ((2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12) *
        (2 : ℝ) ^ (2 * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hp := spaceSplitting_polynomial_le_sourceBudget T N
      have hc : 400000000 * 16384 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
          ((N : ℝ) ^ 2 + 1) ^ 2 ≤
          1280000000 * 16384 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
            ((N : ℝ) ^ 2 + 1) ^ 2 := by gcongr; norm_num
      exact hc.trans hp
    _ ≤ (2 : ℝ) ^ (E / 8) * (2 : ℝ) ^ (2 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hpar.2.1 (by positivity)
    _ ≤ _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

theorem spaceSplitting_decay_ratio_pow_le {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    ((2 : ℝ) ^ (-15 * (tolerance θ N * N) / 8)) ^ expansionCount θ N ≤
      (2 : ℝ) ^ (-450 * (N : ℝ)) := by
  have he := mul_le_mul_of_nonneg_right
    (expansionCount_mul_tolerance_ge θ (N := N) (by have := hpar.1; omega))
    (Nat.cast_nonneg N)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

end FalconerThetaGauge
