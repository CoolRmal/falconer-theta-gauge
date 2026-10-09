module

public import FalconerThetaGauge.StationaryCircularInversionScale

/-! # Explicit source inversion-tail decay and the final pointwise power budget -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

theorem stationary_inverse_scale_le_remainder {T : ℕ} {M : ℝ} (hM : 0 ≤ M) :
    800 * (2 * T) * M ^ 2 ≤
      circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) := by
  have ht₀ : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
  have ht : (T : ℝ) ≤ ((T : ℝ) + 1) ^ 4 := by
    calc
      _ ≤ (T : ℝ) + 1 := by linarith
      _ ≤ _ := by simpa only [pow_one] using
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (T : ℝ) + 1) (by norm_num : 1 ≤ 4)
  have hfactor : 1600 * (T : ℝ) ≤ 100000000 * ((T : ℝ) + 1) ^ 4 := by
    nlinarith [pow_nonneg (by linarith : 0 ≤ (T : ℝ) + 1) 4]
  have hsq : M ^ 2 ≤ (1200 * (T : ℝ) ^ 2 + M) ^ 2 :=
    pow_le_pow_left₀ hM (by nlinarith [sq_nonneg (T : ℝ)]) 2
  unfold circularStationaryRemainderBase
  calc
    _ = 1600 * (T : ℝ) * M ^ 2 := by ring
    _ ≤ _ := mul_le_mul hfactor hsq (sq_nonneg _) (by positivity)

theorem stationary_decay_ratio_le_half {E : ℝ} (hE : 16 ≤ E) :
    (2 : ℝ) ^ (-(7 * E / 8)) ≤ 1 / 2 := by
  calc
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by norm_num

theorem stationary_decay_ratio_pow_le {T N : ℕ} {E : ℝ}
    (hET : 240 * (N : ℝ) ≤ E * T) :
    ((2 : ℝ) ^ (-(7 * E / 8))) ^ T ≤ (2 : ℝ) ^ (-(210 * (N : ℝ))) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

theorem expansionCount_mul_tolerance_ge (θ : ℝ) {N : ℕ} (hN : 0 < N) :
    240 ≤ tolerance θ N * expansionCount θ N := by
  have hε := tolerance_pos θ hN
  have hceil := Nat.le_ceil (240 / tolerance θ N)
  change 240 / tolerance θ N ≤ (expansionCount θ N : ℝ) at hceil
  simpa only [mul_comm] using (div_le_iff₀ hε).mp hceil

theorem stationary_decay_ratio_pow_le_of_parameters {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    ((2 : ℝ) ^ (-(7 * (tolerance θ N * N) / 8))) ^ expansionCount θ N ≤
      (2 : ℝ) ^ (-(210 * (N : ℝ))) := by
  apply stationary_decay_ratio_pow_le
  have h := mul_le_mul_of_nonneg_right
    (expansionCount_mul_tolerance_ge θ (N := N) (by have := hpar.1; omega))
    (Nat.cast_nonneg N)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem normalized_stationary_error_le_terminal_power {T N : ℕ} (hN : 1 ≤ N)
    {d Q q : ℝ} (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hweight : (Real.sqrt d)⁻¹ ≤ (2 : ℝ) ^ (N : ℝ))
    (horder : 2 * (2 * (T : ℝ) + 1) ≤ (2 : ℝ) ^ (N : ℝ))
    (hQbound : Q ≤ (2 : ℝ) ^ (2 * (N : ℝ)))
    (hqpow : q ^ T ≤ (2 : ℝ) ^ (-(210 * (N : ℝ)))) :
    (Real.sqrt d)⁻¹ * (2 * (2 * (T : ℝ) + 1) * q ^ T + 2 * Q * q ^ T) ≤
      (2 : ℝ) ^ (-(200 * (N : ℝ))) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (N : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hN'
  have hpow : (2 : ℝ) ^ (N : ℝ) ≤ (2 : ℝ) ^ (3 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hcoeff : 2 * (2 * (T : ℝ) + 1) + 2 * Q ≤ (2 : ℝ) ^ (4 * (N : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ (N : ℝ) + (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (2 * (N : ℝ)) := by
        exact add_le_add horder (mul_le_mul htwo hQbound hQ (by norm_num))
      _ ≤ 2 * (2 : ℝ) ^ (3 * (N : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        rw [show (N : ℝ) + 2 * N = 3 * N by ring]
        linarith
      _ ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (3 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  calc
    _ = (Real.sqrt d)⁻¹ * (2 * (2 * (T : ℝ) + 1) + 2 * Q) * q ^ T := by ring
    _ ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (4 * (N : ℝ)) *
        (2 : ℝ) ^ (-(210 * (N : ℝ))) := by gcongr
    _ = (2 : ℝ) ^ (-(205 * (N : ℝ))) := by
      simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end FalconerThetaGauge
