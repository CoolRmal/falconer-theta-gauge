module

public import FalconerThetaGauge.MaskedMattilaSymbolScale

/-! # The actual space-splitting depth pays the squared scheduled-symbol scale -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_mask_factor_le (L : ℕ) (E : ℝ) :
    max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) ≤
      (2 : ℝ) ^ (max (L : ℝ) E - E) := by
  apply max_le
  · exact Real.one_le_rpow (by norm_num) (sub_nonneg.mpr (le_max_right _ _))
  · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := le_max_left (L : ℝ) E; linarith)

theorem spaceSplitting_symbol_scale_squared_shift_le {T N L : ℕ} (hT : 1 ≤ T)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1) (E : ℝ)
    {h v : ℝ} (hgap : 2 * max (L : ℝ) E ≤ v - h) :
    (max 1 (scheduledSymbolScale T E I L)) ^ 2 * (2 : ℝ) ^ (h - v) ≤
      16384 * (T : ℝ) ^ 4 * ((N : ℝ) ^ 2 + 1) ^ 2 * (2 : ℝ) ^ (-2 * E) := by
  have hF : 1 ≤ (2 : ℝ) ^ (max (L : ℝ) E - E) :=
    Real.one_le_rpow (by norm_num) (sub_nonneg.mpr (le_max_right _ _))
  have hM := scheduledSymbolScale_max_one_le hT N E I L hcard hF
    (spaceSplitting_mask_factor_le L E)
  have hs := pow_le_pow_left₀ (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) hM 2
  calc
    _ ≤ (128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
        (2 : ℝ) ^ (max (L : ℝ) E - E)) ^ 2 * (2 : ℝ) ^ (h - v) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = (16384 * (T : ℝ) ^ 4 * ((N : ℝ) ^ 2 + 1) ^ 2) *
        (2 : ℝ) ^ (2 * (max (L : ℝ) E - E) + h - v) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1)) ^ 2 =
        16384 * (T : ℝ) ^ 4 * ((N : ℝ) ^ 2 + 1) ^ 2 by ring]
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) (by positivity)

end FalconerThetaGauge
