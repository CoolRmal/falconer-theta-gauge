module

public import FalconerThetaGauge.StationaryPhaseInverseOperatorBudget
public import FalconerThetaGauge.StationaryPhaseInverseOperatorsRegularity

/-! # The actual omitted coefficients of finite stationary-phase inversion -/

@[expose] public section

noncomputable section

open Finset Polynomial

namespace FalconerThetaGauge

/-- The coefficient of degree `m` in the product of the two literal series truncated at `T`. -/
def stationaryPhaseTruncatedConvolution (T m : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (m + 1), if i < T ∧ m - i < T then
    stationaryPhasePolynomial i * stationaryPhaseInversePolynomial (m - i) else 0

theorem stationaryPhaseTruncatedConvolution_below {T m : ℕ} (hm : m < T) :
    stationaryPhaseTruncatedConvolution T m = if m = 0 then 1 else 0 := by
  rw [stationaryPhaseTruncatedConvolution]
  convert stationaryPhasePolynomial_inverse_convolution m using 1
  apply sum_congr rfl
  intro i hi
  have hin : i ≤ m := by have := mem_range.mp hi; omega
  rw [ite_eq_left (by omega)]

theorem stationaryPhasePolynomial_weightedNorm_uniform {M : ℝ} (hM : 1 ≤ M)
    {i m : ℕ} (hi : i ≤ m) :
    polynomialWeightedNorm (stationaryPhasePolynomial i) M ≤ (800 * m * M ^ 2) ^ i := by
  cases i with
  | zero => simp [stationaryPhasePolynomial_zero, polynomialWeightedNorm_one]
  | succ i =>
    rw [stationaryPhasePolynomial_weightedNorm]
    have hiR : (i + 1 : ℝ) ≤ m := by exact_mod_cast hi
    exact (stationaryPhaseWeightedNorm_le (by omega : 1 ≤ i + 1) hM).trans
      (pow_le_pow_left₀ (by positivity) (by
        simp only [Nat.cast_add, Nat.cast_one]
        gcongr
        linarith) _)

theorem stationaryPhaseInversePolynomial_weightedNorm_uniform_eight {M : ℝ} (hM : 1 ≤ M)
    {i m : ℕ} (hi : i ≤ m) :
    polynomialWeightedNorm (stationaryPhaseInversePolynomial i) M ≤
      (800 * m * M ^ 2) ^ i :=
  (stationaryPhaseInversePolynomial_weightedNorm_uniform hM m hi).trans
    (pow_le_pow_left₀ (by positivity) (by gcongr; norm_num) _)

/-- The omitted coefficient is bounded using the actual recursive polynomials and their norms. -/
theorem stationaryPhaseTruncatedConvolution_weightedNorm_le (T m : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    polynomialWeightedNorm (stationaryPhaseTruncatedConvolution T m) M ≤
      (m + 1) * (800 * m * M ^ 2) ^ m := by
  have hM0 : 0 ≤ M := by linarith
  rw [stationaryPhaseTruncatedConvolution]
  calc
    _ ≤ ∑ i ∈ range (m + 1), polynomialWeightedNorm
        (if i < T ∧ m - i < T then
          stationaryPhasePolynomial i * stationaryPhaseInversePolynomial (m - i) else 0) M :=
      polynomialWeightedNorm_sum_le _ _ hM0
    _ ≤ ∑ _i ∈ range (m + 1), (800 * m * M ^ 2) ^ m := by
      apply sum_le_sum
      intro i hi
      have hin : i ≤ m := by have := mem_range.mp hi; omega
      split_ifs with hpass
      · calc
          _ ≤ polynomialWeightedNorm (stationaryPhasePolynomial i) M *
              polynomialWeightedNorm (stationaryPhaseInversePolynomial (m - i)) M :=
            polynomialWeightedNorm_mul_le _ _ hM0
          _ ≤ (800 * m * M ^ 2) ^ i * (800 * m * M ^ 2) ^ (m - i) :=
            mul_le_mul (stationaryPhasePolynomial_weightedNorm_uniform hM hin)
              (stationaryPhaseInversePolynomial_weightedNorm_uniform_eight hM (Nat.sub_le _ _))
              (polynomialWeightedNorm_nonneg _ hM0) (by positivity)
          _ = _ := by rw [← pow_add, Nat.add_sub_of_le hin]
      · simp only [polynomialWeightedNorm, Polynomial.sum_zero_index]
        positivity
    _ = _ := by simp

theorem stationaryPhaseTruncatedConvolution_natDegree_le (T m : ℕ) :
    (stationaryPhaseTruncatedConvolution T m).natDegree ≤ 2 * m := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hin : i ≤ m := by have := mem_range.mp hi; omega
  split_ifs
  · exact (natDegree_mul_le_of_le (stationaryPhasePolynomial_natDegree_le i)
      (stationaryPhaseInversePolynomial_natDegree_le (m - i))).trans (by omega)
  · simp

/-- The literal high-degree coefficient acts on the actual amplitude with the source tail cost. -/
theorem norm_stationaryPhaseTruncatedConvolution_action_le (T m : ℕ) {G : ℝ → ℂ}
    {A M : ℝ} (hG : IsDerivativeRegular A M (2 * m) G) (φ : ℝ) :
    ‖polynomialDifferentialAction (stationaryPhaseTruncatedConvolution T m) G φ‖ ≤
      A * (m + 1) * (800 * m * M ^ 2) ^ m := by
  have horder : IsDerivativeRegular A M (0 + 2 * m) G := by simpa only [zero_add] using hG
  have h := polynomialDifferentialAction_isDerivativeRegular horder
    (stationaryPhaseTruncatedConvolution T m) (stationaryPhaseTruncatedConvolution_natDegree_le T m)
  have hb := h.bound 0 (le_refl 0) φ
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at hb
  calc
    _ ≤ A * polynomialWeightedNorm (stationaryPhaseTruncatedConvolution T m) M := hb
    _ ≤ A * ((m + 1) * (800 * m * M ^ 2) ^ m) :=
      mul_le_mul_of_nonneg_left (stationaryPhaseTruncatedConvolution_weightedNorm_le T m
        hG.one_le_scale) hG.amplitude_nonneg
    _ = _ := by ring

end FalconerThetaGauge
