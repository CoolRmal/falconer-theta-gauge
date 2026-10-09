module

public import FalconerThetaGauge.SpaceSplittingCaseACoefficient

/-! # Every actual Case A stationary main term is at most R⁻⁴⁰⁰ -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem spaceSplitting_caseA_prefactor_le_terminal {N v : ℕ} (hN : 4 ≤ N)
    (hv : v ≤ N) {h d : ℝ} (hh : h ≤ N)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) :
    Real.sqrt (2 * Real.pi / d) * (32 * ((2 : ℝ) ^ v) ^ (3 / 2 : ℝ)) ≤
      (2 : ℝ) ^ (5 * (N : ℝ)) := by
  have hd' : (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ d := by
    calc
      _ ≤ (2 : ℝ) ^ (-h) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) := by
        nlinarith [show 0 < (2 : ℝ) ^ (-h) by positivity]
      _ ≤ _ := hd
  have hinv := inverse_sqrt_distance_le_terminal hN hd'
  have hsqrt : Real.sqrt (2 * Real.pi / d) ≤ 3 * (2 : ℝ) ^ (N : ℝ) := by
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi), div_eq_mul_inv]
    have hp : Real.sqrt (2 * Real.pi) ≤ 3 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · nlinarith [Real.pi_lt_four]
    exact mul_le_mul hp hinv (inv_nonneg.2 (Real.sqrt_nonneg _)) (by norm_num)
  have hpower : ((2 : ℝ) ^ v) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 * (N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hv' : (v : ℝ) ≤ N := by exact_mod_cast hv
    have := Nat.cast_nonneg (α := ℝ) v
    linarith
  have hconstant : (96 : ℝ) ≤ (2 : ℝ) ^ (2 * (N : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ (8 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by
          have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
          linarith)
  calc
    _ ≤ (3 * (2 : ℝ) ^ (N : ℝ)) * (32 * (2 : ℝ) ^ (2 * (N : ℝ))) :=
      mul_le_mul hsqrt (mul_le_mul_of_nonneg_left hpower (by norm_num))
        (by positivity) (by positivity)
    _ = 96 * (2 : ℝ) ^ (3 * (N : ℝ)) := by
      rw [show (3 * (2 : ℝ) ^ (N : ℝ)) * (32 * (2 : ℝ) ^ (2 * (N : ℝ))) =
        96 * ((2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (2 * (N : ℝ))) by ring,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ (2 : ℝ) ^ (2 * (N : ℝ)) * (2 : ℝ) ^ (3 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

theorem norm_spaceSplittingCaseA_coefficient_moment_le_source
    {θ : ℝ} {N L v j : ℕ} (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest)
    (hcard : I.card ≤ N ^ 2 + 1) (hv : v ≤ N) {h d Φ : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ d) (hΦ : d / 2 ≤ |Φ|)
    (hj : j < expansionCount θ N) {c : ℂ}
    (hc : ‖c‖ ≤ (400 * j *
      (max 1 (scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L)) ^ 2) ^ j) :
    ‖(Real.sqrt (2 * Real.pi / d) : ℂ) * (d : ℂ)⁻¹ ^ j * c *
      spaceSplittingCaseARadialMoment (8 * expansionCount θ N) v j Φ‖ ≤
        (2 : ℝ) ^ (-400 * (N : ℝ)) := by
  have hT : 1 ≤ expansionCount θ N := Nat.ceil_pos.mpr
    (by have := tolerance_pos θ (N := N) (by have := hpar.1; omega); positivity)
  have hd₀ : 0 < d := lt_of_lt_of_le (by positivity) hd
  have he := (mul_le_mul_of_nonneg_left (le_max_right _ _)
    (by norm_num : (0 : ℝ) ≤ 2)).trans hgap
  calc
    _ ≤ Real.sqrt (2 * Real.pi / d) * (32 * ((2 : ℝ) ^ v) ^ (3 / 2 : ℝ)) *
        (1200 * (expansionCount θ N : ℝ) ^ 2 / ((2 : ℝ) ^ v * d)) ^ expansionCount θ N :=
      norm_spaceSplittingCaseA_coefficient_moment_le hT (by omega) hj hd₀ hΦ hc
        (by simpa only [Real.rpow_natCast] using
          spaceSplitting_coefficient_scale_le_quarter hpar I hcard hgap hd)
    _ ≤ (2 : ℝ) ^ (5 * (N : ℝ)) * (2 : ℝ) ^ (-450 * (N : ℝ)) := mul_le_mul
      (spaceSplitting_caseA_prefactor_le_terminal hpar.1 hv hh hd)
      (by simpa only [Real.rpow_natCast] using spaceSplitting_linear_ratio_pow_le hpar he hd)
      (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (-445 * (N : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

end FalconerThetaGauge
