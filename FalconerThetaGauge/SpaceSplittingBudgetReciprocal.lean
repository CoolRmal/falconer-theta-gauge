module

public import FalconerThetaGauge.SpaceSplittingBudgetPolynomial

/-! # Actual dyadic lower distance and frequency bounds control inverse stationary scales -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_inv_frequency_distance_le {r d h v : ℝ}
    (hr : (2 : ℝ) ^ v / 4 ≤ r) (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    (r * d)⁻¹ ≤ (16 / 5 : ℝ) * (2 : ℝ) ^ (h - v) := by
  have hr₀ : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hd₀ : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hl : (5 / 16 : ℝ) * (2 : ℝ) ^ (v - h) ≤ r * d := by
    have hh := mul_le_mul hr hd (by positivity : 0 ≤ (5 / 4 : ℝ) * 2 ^ (-h)) hr₀.le
    convert hh using 1
    rw [show (2 : ℝ) ^ v / 4 * ((5 / 4 : ℝ) * (2 : ℝ) ^ (-h)) =
      (5 / 16 : ℝ) * ((2 : ℝ) ^ v * (2 : ℝ) ^ (-h)) by ring,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp only [sub_eq_add_neg]
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) <
    (5 / 16 : ℝ) * (2 : ℝ) ^ (v - h)) hl
  simp only [one_div] at hi
  convert hi using 1
  rw [mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem spaceSplitting_inv_dyadic_distance_le {d h v : ℝ}
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    ((2 : ℝ) ^ v * d)⁻¹ ≤ (4 / 5 : ℝ) * (2 : ℝ) ^ (h - v) := by
  have hd₀ : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hl : (5 / 4 : ℝ) * (2 : ℝ) ^ (v - h) ≤ (2 : ℝ) ^ v * d := by
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2 : ℝ) ^ v)
    convert hh using 1
    rw [show (2 : ℝ) ^ v * ((5 / 4 : ℝ) * (2 : ℝ) ^ (-h)) =
      (5 / 4 : ℝ) * ((2 : ℝ) ^ v * (2 : ℝ) ^ (-h)) by ring,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp only [sub_eq_add_neg]
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) <
    (5 / 4 : ℝ) * (2 : ℝ) ^ (v - h)) hl
  simp only [one_div] at hi
  convert hi using 1
  rw [mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end FalconerThetaGauge
