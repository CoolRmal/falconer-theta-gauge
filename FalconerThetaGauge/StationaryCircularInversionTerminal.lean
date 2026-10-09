module

public import FalconerThetaGauge.StationaryCircularInversionDecay

/-! # Terminal-scale control of the actual stationary inversion coefficients -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem scheduled_mask_terminal_factor_le {E : ℝ} {N L : ℕ}
    (hE : E ≤ N) (hL : L ≤ N) :
    max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) ≤ (2 : ℝ) ^ ((N : ℝ) - E) := by
  apply max_le
  · exact Real.one_le_rpow (by norm_num) (by linarith)
  · rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by
        have hL' : (L : ℝ) ≤ N := by exact_mod_cast hL
        linarith)

theorem stationary_order_polynomial_le_sourceBudget (T N : ℕ) :
    2 * (2 * (T : ℝ) + 1) ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) := by
  have ht₀ : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
  have hn₀ : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have ht : (T : ℝ) + 1 ≤ ((T : ℝ) + 1) ^ 12 := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (T : ℝ) + 1) (by norm_num : 1 ≤ 12)
  have hn : 1 ≤ ((N : ℝ) + 16) ^ 12 := one_le_pow₀ (by linarith)
  calc
    _ ≤ 4 * ((T : ℝ) + 1) * 1 := by linarith
    _ ≤ _ := mul_le_mul
      (mul_le_mul (by norm_num : (4 : ℝ) ≤ 2 ^ (80 : ℕ)) ht (by positivity)
        (by positivity)) hn (by norm_num) (by positivity)

theorem prepared_stationary_remainder_le_terminal {T N : ℕ}
    {E M : ℝ} (hE₀ : 0 ≤ E) (hE : E ≤ N) (hM₀ : 0 ≤ M)
    (hM : M ≤ 256 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ ((N : ℝ) - E))
    (hP1 : (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
      ((N : ℝ) + 16) ^ (12 : ℕ) ≤ (2 : ℝ) ^ (E / 8)) :
    circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) ≤
      (2 : ℝ) ^ (2 * (N : ℝ)) := by
  have hf : 1 ≤ (2 : ℝ) ^ ((N : ℝ) - E) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hprod : 1 ≤ ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ ((N : ℝ) - E) := by
    nlinarith [sq_nonneg (N : ℝ)]
  have h := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 1792 * (T : ℝ) ^ 2)
  have hscale : 1200 * (T : ℝ) ^ 2 + M ≤
      2048 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ ((N : ℝ) - E) := by
    nlinarith
  have hpoly : 100000000 * 2048 ^ 2 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
      ((N : ℝ) ^ 2 + 1) ^ 2 ≤ (2 : ℝ) ^ (E / 8) := by
    apply le_trans _ ((stationary_remainder_polynomial_le_sourceBudget T N).trans hP1)
    nlinarith [show 0 ≤ ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
      ((N : ℝ) ^ 2 + 1) ^ 2 by positivity]
  calc
    _ ≤ 100000000 * ((T : ℝ) + 1) ^ 4 *
        (2048 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ ((N : ℝ) - E)) ^ 2 := by
      unfold circularStationaryRemainderBase
      gcongr
    _ = (100000000 * 2048 ^ 2 * ((T : ℝ) + 1) ^ 4 * (T : ℝ) ^ 4 *
        ((N : ℝ) ^ 2 + 1) ^ 2) * ((2 : ℝ) ^ ((N : ℝ) - E)) ^ 2 := by ring
    _ ≤ (2 : ℝ) ^ (E / 8) * ((2 : ℝ) ^ ((N : ℝ) - E)) ^ 2 :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = (2 : ℝ) ^ (E / 8 + ((N : ℝ) - E) * 2) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [Nat.cast_ofNat]
      rw [← Real.rpow_add (by norm_num)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem parameterFacts_tolerance_le_one {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    tolerance θ N ≤ 1 := by
  have hP4 := hpar.2.2.2.2
  have hk : blockParameter θ N ≤ 1 / 10000 := hP4.2.1.trans hP4.2.2.1
  have hk₀ : 0 < blockParameter θ N := blockParameter_pos θ (by have := hpar.1; omega)
  have hε := hP4.2.2.2.2.1
  nlinarith

theorem stationary_order_le_terminal_of_parameters {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    2 * (2 * (expansionCount θ N : ℝ) + 1) ≤ (2 : ℝ) ^ (N : ℝ) := by
  have hE : tolerance θ N * N ≤ (N : ℝ) :=
    by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (parameterFacts_tolerance_le_one hpar) (Nat.cast_nonneg N)
  calc
    _ ≤ (2 : ℝ) ^ (tolerance θ N * N / 8) :=
      (stationary_order_polynomial_le_sourceBudget _ _).trans hpar.2.1
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

theorem inverse_sqrt_distance_le_terminal {N : ℕ} (hN : 4 ≤ N) {d : ℝ}
    (hd : (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ d) :
    (Real.sqrt d)⁻¹ ≤ (2 : ℝ) ^ (N : ℝ) := by
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlower : (2 : ℝ) ^ (-(2 * (N : ℝ))) ≤ d :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)).trans hd
  have hs : Real.sqrt ((2 : ℝ) ^ (-(2 * (N : ℝ)))) = (2 : ℝ) ^ (-(N : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hroot := Real.sqrt_le_sqrt hlower
  rw [hs] at hroot
  calc
    _ ≤ ((2 : ℝ) ^ (-(N : ℝ)))⁻¹ := inv_anti₀ (by positivity) hroot
    _ = _ := by rw [Real.rpow_neg (by norm_num), inv_inv]

end FalconerThetaGauge
