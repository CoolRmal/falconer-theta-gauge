module

public import FalconerThetaGauge.StationaryPhaseCompositionNorms

/-! # Actual weighted norms of the universal stationary phase coefficients -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

def stationaryDerivativeWeightedNorm (n : ℕ) (M : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), ‖stationaryDerivativeCoefficient n k‖ * M ^ k

def stationaryPhaseWeightedNorm (j : ℕ) (M : ℝ) : ℝ :=
  ∑ k ∈ range (2 * j + 1), ‖stationaryPhaseCoefficient j k‖ * M ^ k

theorem stationaryDerivativeWeightedNorm_le (n : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    stationaryDerivativeWeightedNorm n M ≤
      2 * (n + 1) * (n.factorial : ℝ) * (2 * M) ^ n := by
  classical
  have hM0 : 0 ≤ M := by linarith
  unfold stationaryDerivativeWeightedNorm
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        (∑ i ∈ range (n + 1),
          (n.choose i : ℝ) * ‖iteratedDeriv i stationaryMorseJacobian 0‖ *
            ‖stationaryCompositionCoefficient (n - i) k‖) * M ^ k := by
      apply sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM0 _)
      calc
        _ ≤ ∑ i ∈ range (n + 1),
            ‖(n.choose i : ℝ) * iteratedDeriv i stationaryMorseJacobian 0 *
              stationaryCompositionCoefficient (n - i) k‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_mul, Real.norm_natCast]
    _ = ∑ i ∈ range (n + 1),
        (n.choose i : ℝ) * ‖iteratedDeriv i stationaryMorseJacobian 0‖ *
          stationaryCompositionWeightedNorm (n - i) n M := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [stationaryCompositionWeightedNorm, mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ ∑ i ∈ range (n + 1),
        (n.choose i : ℝ) * (2 * (i.factorial : ℝ) * 2 ^ i) *
          ((2 * M) ^ (n - i) * ((n - i).factorial : ℝ)) := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (norm_iteratedDeriv_stationaryMorseJacobian_le i (by norm_num)) (Nat.cast_nonneg _)
      · exact stationaryCompositionWeightedNorm_le (Nat.sub_le n i) hM
      · unfold stationaryCompositionWeightedNorm
        exact sum_nonneg (fun k _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hM0 _))
      · positivity
    _ = 2 * (n.factorial : ℝ) *
        ∑ i ∈ range (n + 1), 2 ^ i * (2 * M) ^ (n - i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have hc : (n.choose i : ℝ) * (i.factorial : ℝ) *
          ((n - i).factorial : ℝ) = (n.factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
      calc
        _ = 2 * ((n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ)) *
            (2 ^ i * (2 * M) ^ (n - i)) := by ring
        _ = _ := by rw [hc]
    _ ≤ 2 * (n.factorial : ℝ) * ∑ _i ∈ range (n + 1), (2 * M) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
      calc
        _ ≤ (2 * M) ^ i * (2 * M) ^ (n - i) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
          exact pow_le_pow_left₀ (by norm_num) (by linarith) _
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hin]
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

theorem stationaryPhaseWeightedNorm_eq (j : ℕ) (M : ℝ) :
    stationaryPhaseWeightedNorm j M = (2 : ℝ)⁻¹ ^ j / (j.factorial : ℝ) *
      stationaryDerivativeWeightedNorm (2 * j) M := by
  unfold stationaryPhaseWeightedNorm stationaryDerivativeWeightedNorm
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  rw [stationaryPhaseCoefficient, norm_mul, norm_div, norm_pow, norm_div]
  simp only [Complex.norm_I, Complex.norm_ofNat, one_div, Complex.norm_natCast,
    Complex.norm_real]
  ring

end FalconerThetaGauge
