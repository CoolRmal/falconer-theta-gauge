module

public import FalconerThetaGauge.SpaceSplittingStationaryMainIntegral
public import FalconerThetaGauge.SpaceSplittingRadialLinear
public import FalconerThetaGauge.SpaceSplittingCaseABudget

/-! # Actual equal-sign coefficients preserve the radial cancellation budget -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem norm_spaceSplitting_equal_coefficient_moment_le {T K v j k : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j < T) (hk : k < T)
    {dx dy δ M : ℝ} (hx : 0 < dx) (hy : 0 < dy) (hδ : dx ≤ |δ|)
    {c c' : ℂ} (hc : ‖c‖ ≤ (400 * j * M ^ 2) ^ j)
    (hc' : ‖c'‖ ≤ (400 * k * M ^ 2) ^ k)
    (hxscale : 1600 * T * M ^ 2 / ((2 : ℝ) ^ v * dx) ≤ 1 / 4)
    (hyscale : 1600 * T * M ^ 2 / ((2 : ℝ) ^ v * dy) ≤ 1 / 4) :
    ‖(c / (dx : ℂ) ^ j) * (c' / (dy : ℂ) ^ k) *
        spaceSplittingRadialMoment K v (1 - (j : ℤ) - k) δ‖ ≤
      16 * (2 : ℝ) ^ v *
        (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * dx)) ^ T := by
  have hs : 0 < (2 : ℝ) ^ v := by positivity
  have hδ₀ : 0 < |δ| := hx.trans_le hδ
  have hm := norm_spaceSplittingRadialMoment_le_linear (v := v) hT hK
    (stationary_orders_abs_le_two_order hT hj hk) (abs_pos.1 hδ₀)
  have hb := spaceSplittingRadialBound_orders_le v j k
  rw [dyadic_stationary_order_power] at hb
  have hx' := stationary_coefficient_scaled_le_geometric hx hs hj.le hc hxscale
  have hy' := stationary_coefficient_scaled_le_geometric hy hs hk.le hc' hyscale
  have hr : 600 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * |δ|) ≤
      1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * dx) := by
    calc
      _ ≤ 600 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * dx) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hs hx)
          (mul_le_mul_of_nonneg_left hδ hs.le)
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (T : ℝ)])
        (mul_nonneg hs.le hx.le)
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hy]
  calc
    _ ≤ (‖c‖ / dx ^ j * (‖c'‖ / dy ^ k)) *
        (4 * ((4 : ℝ) ^ (j + k + 1) *
          ((2 : ℝ) ^ v / (((2 : ℝ) ^ v) ^ j * ((2 : ℝ) ^ v) ^ k))) *
          (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * dx)) ^ T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hm.trans (mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num))
        (pow_le_pow_left₀ (by positivity) hr T) (by positivity) (by positivity))
    _ = (16 * (2 : ℝ) ^ v) *
        ((‖c‖ * (4 / ((2 : ℝ) ^ v * dx)) ^ j) *
          (‖c'‖ * (4 / ((2 : ℝ) ^ v * dy)) ^ k)) *
        (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * dx)) ^ T := by
      simp only [pow_add, pow_succ, div_pow, mul_pow]
      field_simp [hx.ne', hy.ne', hs.ne']
      ring
    _ ≤ _ := by
      have hcoef : (‖c‖ * (4 / ((2 : ℝ) ^ v * dx)) ^ j) *
          (‖c'‖ * (4 / ((2 : ℝ) ^ v * dy)) ^ k) ≤ 1 := by
        exact (mul_le_mul hx' hy' (by positivity) (by positivity)).trans
          (by rw [← pow_add]; exact pow_le_one₀ (by norm_num) (by norm_num))
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef (by positivity : 0 ≤ 16 * (2 : ℝ) ^ v))
        (by positivity : 0 ≤ (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * dx)) ^ T)

end FalconerThetaGauge
