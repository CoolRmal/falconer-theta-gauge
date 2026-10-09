module

public import FalconerThetaGauge.SpaceSplittingCaseABudget

/-! # Actual real-power radial moments multiplied by stationary coefficients -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_caseA_bound_coefficient_eq (v j : ℕ) (d : ℝ) (c : ℂ)
    (hd : 0 < d) :
    ‖c‖ * d⁻¹ ^ j * (4 * (2 : ℝ) ^ v * spaceSplittingCaseABound v j) =
      32 * ((2 : ℝ) ^ v) ^ (3 / 2 : ℝ) *
        (‖c‖ * (4 / ((2 : ℝ) ^ v * d)) ^ j) := by
  unfold spaceSplittingCaseABound
  rw [Real.rpow_sub (by positivity : 0 < (2 : ℝ) ^ v), Real.rpow_natCast]
  rw [div_pow, mul_pow, inv_pow]
  field_simp [hd.ne']
  ring

theorem norm_spaceSplittingCaseA_coefficient_moment_le {T K v j : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j < T) {d Φ M : ℝ} (hd : 0 < d)
    (hΦ : d / 2 ≤ |Φ|) {c : ℂ} (hc : ‖c‖ ≤ (400 * j * M ^ 2) ^ j)
    (hscale : 1600 * T * M ^ 2 / ((2 : ℝ) ^ v * d) ≤ 1 / 4) :
    ‖(Real.sqrt (2 * Real.pi / d) : ℂ) * (d : ℂ)⁻¹ ^ j * c *
      spaceSplittingCaseARadialMoment K v j Φ‖ ≤
        Real.sqrt (2 * Real.pi / d) * (32 * ((2 : ℝ) ^ v) ^ (3 / 2 : ℝ)) *
          (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ T := by
  have hh := norm_spaceSplittingCaseARadialMoment_le_linear (v := v) hT hK hj hd hΦ
  have hc' := stationary_coefficient_scaled_le_geometric hd (by positivity) hj.le hc hscale
  have hg : (1 / (4 : ℝ)) ^ j ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hd,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (2 * Real.pi / d) * d⁻¹ ^ j * ‖c‖ *
        (4 * (2 : ℝ) ^ v * spaceSplittingCaseABound v j *
          (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ T) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = Real.sqrt (2 * Real.pi / d) *
        (32 * ((2 : ℝ) ^ v) ^ (3 / 2 : ℝ)) *
        (‖c‖ * (4 / ((2 : ℝ) ^ v * d)) ^ j) *
        (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ T := by
      have he := spaceSplitting_caseA_bound_coefficient_eq v j d c hd
      calc
        _ = Real.sqrt (2 * Real.pi / d) *
            (‖c‖ * d⁻¹ ^ j * (4 * (2 : ℝ) ^ v * spaceSplittingCaseABound v j)) *
            (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ T := by ring
        _ = _ := by rw [he]; ring
    _ ≤ _ := by
      have hh' := mul_le_mul_of_nonneg_left (hc'.trans hg)
        (by positivity : 0 ≤ Real.sqrt (2 * Real.pi / d) *
          (32 * ((2 : ℝ) ^ v) ^ (3 / 2 : ℝ)))
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hh'
        (by positivity : 0 ≤ (1200 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ T)

end FalconerThetaGauge
