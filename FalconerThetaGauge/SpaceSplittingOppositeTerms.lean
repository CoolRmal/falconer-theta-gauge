module

public import FalconerThetaGauge.SpaceSplittingRadialOrders
public import FalconerThetaGauge.SpaceSplittingCoefficientSum

/-! # Actual opposite-sign radial stationary terms -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

theorem dyadic_stationary_order_power (v j k : ℕ) :
    (2 : ℝ) ^ ((v : ℝ) * (1 - (j : ℝ) - k)) =
      (2 : ℝ) ^ v / (((2 : ℝ) ^ v) ^ j * ((2 : ℝ) ^ v) ^ k) := by
  have hs : 0 < (2 : ℝ) ^ v := by positivity
  calc
    _ = ((2 : ℝ) ^ v) ^ (1 - (j : ℤ) - k) := by
      rw [← Real.rpow_intCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      rfl
    _ = _ := by
      rw [zpow_sub₀ hs.ne', zpow_sub₀ hs.ne', zpow_one, zpow_natCast, zpow_natCast]
      ring

/-- This is one literal opposite-sign term before its common `2π / √(dₓdᵧ)` factor. -/
def spaceSplittingOppositeTerm (K v j k : ℕ) (dx dy : ℝ) (c c' : ℂ) : ℂ :=
  (c / (dx : ℂ) ^ j) * (c' / (dy : ℂ) ^ k) *
    spaceSplittingRadialMoment K v (1 - (j : ℤ) - k) (dx - dy)

theorem norm_spaceSplittingOppositeTerm_le {K v T j k : ℕ} (hK : 2 ≤ K)
    {dx dy : ℝ} (hdx : 0 < dx) (hdy : 0 < dy) (hj : j ≤ T) (hk : k ≤ T)
    {M : ℝ} {c c' : ℂ}
    (hc : ‖c‖ ≤ (400 * j * M ^ 2) ^ j)
    (hc' : ‖c'‖ ≤ (400 * k * M ^ 2) ^ k)
    (hxscale : 1600 * T * M ^ 2 / ((2 : ℝ) ^ v * dx) ≤ 1 / 4)
    (hyscale : 1600 * T * M ^ 2 / ((2 : ℝ) ^ v * dy) ≤ 1 / 4) :
    ‖spaceSplittingOppositeTerm K v j k dx dy c c'‖ ≤
      50176 * (2 : ℝ) ^ v * ((j : ℝ) + k + 2) ^ 2 * (1 / (4 : ℝ)) ^ (j + k) /
        (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2 := by
  have hs : 0 < (2 : ℝ) ^ v := by positivity
  have hx := stationary_coefficient_scaled_le_geometric hdx hs hj hc hxscale
  have hy := stationary_coefficient_scaled_le_geometric hdy hs hk hc' hyscale
  have hm := norm_spaceSplittingRadialMoment_orders_le (v := v) hK j k (dx - dy)
  rw [dyadic_stationary_order_power] at hm
  have hn : 0 ≤ ‖c‖ / dx ^ j * (‖c'‖ / dy ^ k) := by positivity
  calc
    _ = (‖c‖ / dx ^ j * (‖c'‖ / dy ^ k)) *
        ‖spaceSplittingRadialMoment K v (1 - (j : ℤ) - k) (dx - dy)‖ := by
      simp only [spaceSplittingOppositeTerm, norm_mul, norm_div, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdx, abs_of_pos hdy]
    _ ≤ (‖c‖ / dx ^ j * (‖c'‖ / dy ^ k)) *
        (12544 * ((j : ℝ) + k + 2) ^ 2 * (4 : ℝ) ^ (j + k + 1) *
          ((2 : ℝ) ^ v / (((2 : ℝ) ^ v) ^ j * ((2 : ℝ) ^ v) ^ k)) /
            (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) := mul_le_mul_of_nonneg_left hm hn
    _ = (50176 * (2 : ℝ) ^ v * ((j : ℝ) + k + 2) ^ 2 /
        (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) *
          ((‖c‖ * (4 / ((2 : ℝ) ^ v * dx)) ^ j) *
            (‖c'‖ * (4 / ((2 : ℝ) ^ v * dy)) ^ k)) := by
      rw [pow_add, pow_succ, div_pow, div_pow, mul_pow, mul_pow]
      field_simp
      ring
    _ ≤ (50176 * (2 : ℝ) ^ v * ((j : ℝ) + k + 2) ^ 2 /
        (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) *
          ((1 / (4 : ℝ)) ^ j * (1 / (4 : ℝ)) ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hx hy (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

end FalconerThetaGauge
