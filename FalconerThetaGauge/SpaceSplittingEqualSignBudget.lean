module

public import FalconerThetaGauge.SpaceSplittingEqualSignTerms
public import FalconerThetaGauge.SpaceSplittingCaseASource

/-! # Source-scale decay of every actual equal-sign stationary term -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_equal_prefactor_le_terminal {N v : ℕ}
    (hN : 4 ≤ N) (hv : v ≤ N) {h dx dy : ℝ} (hh : h ≤ N)
    (hdx : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dx)
    (hdy : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dy) :
    (2 * Real.pi / Real.sqrt (dx * dy)) * (16 * (2 : ℝ) ^ v) ≤
      (2 : ℝ) ^ (5 * (N : ℝ)) := by
  have hx : 0 < dx := lt_of_lt_of_le (by positivity) hdx
  have hy : 0 < dy := lt_of_lt_of_le (by positivity) hdy
  have hlow {d : ℝ} (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
      (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ d := by
    calc
      _ ≤ (2 : ℝ) ^ (-h) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) := by
        nlinarith [show 0 < (2 : ℝ) ^ (-h) by positivity]
      _ ≤ _ := hd
  have hi : (Real.sqrt (dx * dy))⁻¹ ≤ (2 : ℝ) ^ (2 * (N : ℝ)) := by
    rw [Real.sqrt_mul hx.le, mul_inv_rev]
    have hh' := mul_le_mul (inverse_sqrt_distance_le_terminal hN (hlow hdy))
      (inverse_sqrt_distance_le_terminal hN (hlow hdx)) (by positivity) (by positivity)
    convert hh' using 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hs : (2 : ℝ) ^ v ≤ (2 : ℝ) ^ (N : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hv)
  have hconstant : (128 : ℝ) ≤ (2 : ℝ) ^ (2 * (N : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ (8 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by
          have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
          linarith)
  calc
    _ ≤ (8 * (2 : ℝ) ^ (2 * (N : ℝ))) * (16 * (2 : ℝ) ^ (N : ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul (by nlinarith [Real.pi_lt_four]) hi
        (by positivity) (by norm_num)) (mul_le_mul_of_nonneg_left hs (by norm_num))
        (by positivity) (by positivity)
    _ = 128 * (2 : ℝ) ^ (3 * (N : ℝ)) := by
      rw [show (8 * (2 : ℝ) ^ (2 * (N : ℝ))) * (16 * (2 : ℝ) ^ (N : ℝ)) =
        128 * ((2 : ℝ) ^ (2 * (N : ℝ)) * (2 : ℝ) ^ (N : ℝ)) by ring,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ (2 : ℝ) ^ (2 * (N : ℝ)) * (2 : ℝ) ^ (3 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

theorem norm_spaceSplitting_equal_coefficient_moment_le_source
    {θ : ℝ} {N L v j k : ℕ} (hpar : ParameterFacts θ N)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1) (hv : v ≤ N)
    {h dx dy δ : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    (hdx : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dx)
    (hdy : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dy) (hδ : dx ≤ |δ|)
    (hj : j < expansionCount θ N) (hk : k < expansionCount θ N) {c c' : ℂ}
    (hc : ‖c‖ ≤ (400 * j *
      (max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) ^ 2) ^ j)
    (hc' : ‖c'‖ ≤ (400 * k *
      (max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) ^ 2) ^ k) :
    ‖(2 * Real.pi / Real.sqrt (dx * dy) : ℝ) *
        ((c / (dx : ℂ) ^ j) * (c' / (dy : ℂ) ^ k) *
          spaceSplittingRadialMoment (8 * expansionCount θ N) v
            (1 - (j : ℤ) - k) δ)‖ ≤ (2 : ℝ) ^ (-400 * (N : ℝ)) := by
  have hT : 1 ≤ expansionCount θ N := Nat.ceil_pos.mpr
    (by have := tolerance_pos θ (N := N) (by have := hpar.1; omega); positivity)
  have hx : 0 < dx := lt_of_lt_of_le (by positivity) hdx
  have hy : 0 < dy := lt_of_lt_of_le (by positivity) hdy
  have he := (mul_le_mul_of_nonneg_left (le_max_right _ _)
    (by norm_num : (0 : ℝ) ≤ 2)).trans hgap
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (2 * Real.pi / Real.sqrt (dx * dy)) * (16 * (2 : ℝ) ^ v *
        (1200 * (expansionCount θ N : ℝ) ^ 2 / ((2 : ℝ) ^ v * dx)) ^
          expansionCount θ N) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact norm_spaceSplitting_equal_coefficient_moment_le hT (by omega) hj hk hx hy hδ
        hc hc' (by simpa only [Real.rpow_natCast] using
          spaceSplitting_coefficient_scale_le_quarter hpar I hcard hgap hdx)
        (by simpa only [Real.rpow_natCast] using
          spaceSplitting_coefficient_scale_le_quarter hpar I hcard hgap hdy)
    _ ≤ (2 : ℝ) ^ (5 * (N : ℝ)) * (2 : ℝ) ^ (-450 * (N : ℝ)) := by
      rw [← mul_assoc]
      exact mul_le_mul (spaceSplitting_equal_prefactor_le_terminal hpar.1 hv hh hdx hdy)
        (by simpa only [Real.rpow_natCast] using
          spaceSplitting_linear_ratio_pow_le hpar he hdx) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (-445 * (N : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

theorem two_stationary_count_square_le_terminal {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    2 * (expansionCount θ N : ℝ) ^ 2 ≤ (2 : ℝ) ^ (N : ℝ) := by
  have hp := (spaceSplitting_linear_polynomial_le_sourceBudget (expansionCount θ N) N).trans
    hpar.2.1
  have hE : tolerance θ N * N ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (parameterFacts_tolerance_le_one hpar) (Nat.cast_nonneg N)
  calc
    _ ≤ 960 * (expansionCount θ N : ℝ) ^ 2 := by nlinarith [sq_nonneg (expansionCount θ N : ℝ)]
    _ ≤ (2 : ℝ) ^ (tolerance θ N * N / 8) := hp
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

end FalconerThetaGauge
