module

public import FalconerThetaGauge.OrthogonalityAngularNonstationary
public import FalconerThetaGauge.StationaryCircularInversionDecay

/-! # The exact parameter budget turns genuine angular integration by parts into R^-90 -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

open GaugeFrostman

theorem orthogonality_angular_polynomial_le_sourceBudget (T N : ℕ) :
    32768 * ((T : ℝ) + 1) ^ 2 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12 := by
  have hT : (T : ℝ) ^ 2 ≤ ((T : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
  have hN : (N : ℝ) ^ 2 + 1 ≤ ((N : ℝ) + 16) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hTp : ((T : ℝ) + 1) ^ 4 ≤ ((T : ℝ) + 1) ^ 12 :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith) (by norm_num)
  have hNp : ((N : ℝ) + 16) ^ 2 ≤ ((N : ℝ) + 16) ^ 12 :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by norm_num)
  calc
    _ ≤ (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 2 * ((T : ℝ) + 1) ^ 2 *
        ((N : ℝ) + 16) ^ 2 := by gcongr; norm_num
    _ = (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 4 * ((N : ℝ) + 16) ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem orthogonality_angular_decay_ratio_le {T N p v : ℕ} {E Ma q lam : ℝ}
    (hMa : Ma ≤ 1024 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ ((v : ℝ) - p + E))
    (hq : q ≤ 1024 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
      (2 : ℝ) ^ ((v : ℝ) - p + E))
    (hlam : (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2) ≤ lam)
    (hP1 : (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ 12 * ((N : ℝ) + 16) ^ 12 ≤
      (2 : ℝ) ^ (E / 8)) :
    2 * (T + 1 : ℝ) ^ 2 * max Ma q / lam ≤ (2 : ℝ) ^ (-(3 * E / 8)) := by
  have hLam₀ : 0 < (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2) := by positivity
  calc
    _ ≤ (2 * (T + 1 : ℝ) ^ 2 * (1024 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) *
        (2 : ℝ) ^ ((v : ℝ) - p + E))) /
        (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2) := by
      apply div_le_div₀ (by positivity) _ hLam₀ hlam
      exact mul_le_mul_of_nonneg_left (max_le hMa hq) (by positivity)
    _ = (32768 * ((T : ℝ) + 1) ^ 2 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1)) *
        (2 : ℝ) ^ (-E / 2) := by
      calc
        _ = (2048 * ((T : ℝ) + 1) ^ 2 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1)) *
            ((2 : ℝ) ^ ((v : ℝ) - p + E) /
              (2 : ℝ) ^ ((v : ℝ) - p - 4 + 3 * E / 2)) := by ring
        _ = _ := by
          rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
            show (v : ℝ) - p + E - ((v : ℝ) - p - 4 + 3 * E / 2) =
              4 + -E / 2 by ring, Real.rpow_add (by norm_num)]
          norm_num
          ring
    _ ≤ (2 : ℝ) ^ (E / 8) * (2 : ℝ) ^ (-E / 2) :=
      mul_le_mul_of_nonneg_right
        ((orthogonality_angular_polynomial_le_sourceBudget T N).trans hP1) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

theorem orthogonality_angular_decay_pow_le {T N : ℕ} {E : ℝ}
    (hET : 240 * (N : ℝ) ≤ E * T) :
    ((2 : ℝ) ^ (-(3 * E / 8))) ^ T ≤ (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

theorem orthogonality_angular_decay_pow_le_of_parameters {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) :
    ((2 : ℝ) ^ (-(3 * (tolerance θ N * N) / 8))) ^ expansionCount θ N ≤
      (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
  apply orthogonality_angular_decay_pow_le
  have h := mul_le_mul_of_nonneg_right
    (expansionCount_mul_tolerance_ge θ (N := N) (by have := hpar.1; omega))
    (Nat.cast_nonneg N)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end FalconerThetaGauge
