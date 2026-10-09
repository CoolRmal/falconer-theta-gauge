module

public import FalconerThetaGauge.SpaceSplittingBudgetReciprocal

/-! # Literal source equation 7.5 from actual scheduled scales and ParameterFacts -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_remainder_ratio_le {θ : ℝ} {N L : ℕ}
    (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    {h v r d : ℝ} (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ v - h)
    (hr : (2 : ℝ) ^ v / 4 ≤ r) (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    circularStationaryRemainderBase (expansionCount θ N)
        (2 * max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) /
        (r * d) ≤ (2 : ℝ) ^ (-15 * (tolerance θ N * N) / 8) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let M := max 1 (scheduledSymbolScale T E I L)
  have hN : 0 < N := by have := hpar.1; omega
  have hT : 1 ≤ T := Nat.ceil_pos.mpr (by have := tolerance_pos θ hN; positivity)
  have hs := spaceSplitting_symbol_scale_squared_shift_le hT I hcard E hgap
  have hi := spaceSplitting_inv_frequency_distance_le hr hd
  change circularStationaryRemainderBase T (2 * M) / (r * d) ≤ _
  rw [spaceSplitting_remainderBase_eq, div_eq_mul_inv]
  calc
    _ ≤ (400000000 * ((T : ℝ) + 1) ^ 4 * M ^ 2) *
        ((16 / 5 : ℝ) * (2 : ℝ) ^ (h - v)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (1280000000 * ((T : ℝ) + 1) ^ 4) * (M ^ 2 * (2 : ℝ) ^ (h - v)) := by ring
    _ ≤ (1280000000 * ((T : ℝ) + 1) ^ 4) *
        (16384 * (T : ℝ) ^ 4 * ((N : ℝ) ^ 2 + 1) ^ 2 * (2 : ℝ) ^ (-2 * E)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (1280000000 * 16384 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
        ((N : ℝ) ^ 2 + 1) ^ 2) * (2 : ℝ) ^ (-2 * E) := by ring
    _ ≤ ((2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12) *
        (2 : ℝ) ^ (-2 * E) := mul_le_mul_of_nonneg_right
      (spaceSplitting_polynomial_le_sourceBudget T N) (by positivity)
    _ ≤ (2 : ℝ) ^ (E / 8) * (2 : ℝ) ^ (-2 * E) :=
      mul_le_mul_of_nonneg_right hpar.2.1 (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [E]
      ring

theorem spaceSplitting_coefficient_scale_le {θ : ℝ} {N L : ℕ}
    (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    {h v d : ℝ} (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ v - h)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    1600 * (expansionCount θ N : ℝ) *
        (max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) ^ 2 /
        ((2 : ℝ) ^ v * d) ≤ (2 : ℝ) ^ (-15 * (tolerance θ N * N) / 8) := by
  let T := expansionCount θ N
  let E := tolerance θ N * N
  let M := max 1 (scheduledSymbolScale T E I L)
  have hN : 0 < N := by have := hpar.1; omega
  have hT : 1 ≤ T := Nat.ceil_pos.mpr (by have := tolerance_pos θ hN; positivity)
  have hs := spaceSplitting_symbol_scale_squared_shift_le hT I hcard E hgap
  have hi := spaceSplitting_inv_dyadic_distance_le (v := v) hd
  change 1600 * (T : ℝ) * M ^ 2 / ((2 : ℝ) ^ v * d) ≤ _
  rw [div_eq_mul_inv]
  calc
    _ ≤ (1600 * (T : ℝ) * M ^ 2) * ((4 / 5 : ℝ) * (2 : ℝ) ^ (h - v)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (1280 * (T : ℝ)) * (M ^ 2 * (2 : ℝ) ^ (h - v)) := by ring
    _ ≤ (1280 * (T : ℝ)) *
        (16384 * (T : ℝ) ^ 4 * ((N : ℝ) ^ 2 + 1) ^ 2 * (2 : ℝ) ^ (-2 * E)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (1280 * 16384 * (T : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 1) ^ 2) *
        (2 : ℝ) ^ (-2 * E) := by ring
    _ ≤ ((2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12) *
        (2 : ℝ) ^ (-2 * E) := mul_le_mul_of_nonneg_right
      (spaceSplitting_coefficient_polynomial_le_sourceBudget T N) (by positivity)
    _ ≤ (2 : ℝ) ^ (E / 8) * (2 : ℝ) ^ (-2 * E) :=
      mul_le_mul_of_nonneg_right hpar.2.1 (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [E]
      ring

theorem spaceSplitting_coefficient_scale_le_quarter {θ : ℝ} {N L : ℕ}
    (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    {h v d : ℝ} (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ v - h)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    1600 * (expansionCount θ N : ℝ) *
        (max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) ^ 2 /
        ((2 : ℝ) ^ v * d) ≤ 1 / 4 := by
  apply (spaceSplitting_coefficient_scale_le hpar I hcard hgap hd).trans
  calc
    _ ≤ (2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := hpar.2.2.1.1; linarith)
    _ = _ := by norm_num

end FalconerThetaGauge
