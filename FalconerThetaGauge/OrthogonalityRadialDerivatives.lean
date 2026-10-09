module

public import FalconerThetaGauge.OrthogonalityRadialAmplitude

/-! # Actual radial derivative bounds with scales that may be smaller than one -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_mul_le_at {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {A B M P : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hM : 0 ≤ M) (_hP : 0 ≤ P) (k : ℕ) (x : ℝ)
    (hfb : ∀ j ≤ k, ‖iteratedDeriv j f x‖ ≤ A * M ^ j)
    (hgb : ∀ j ≤ k, ‖iteratedDeriv j g x‖ ≤ B * P ^ j) :
    ‖iteratedDeriv k (f * g) x‖ ≤ (A * B) * (M + P) ^ k := by
  have hle := ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) k
  rw [iteratedDeriv_mul (hf.of_le hle).contDiffAt (hg.of_le hle).contDiffAt]
  calc
    _ ≤ ∑ j ∈ range (k + 1),
        ‖(k.choose j : ℂ) * iteratedDeriv j f x * iteratedDeriv (k - j) g x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ range (k + 1),
        (k.choose j : ℝ) * (A * M ^ j) * (B * P ^ (k - j)) := by
      apply sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfb j hjk) (Nat.cast_nonneg _))
        (hgb (k - j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hA (pow_nonneg hM _)))
    _ = _ := by
      rw [add_pow, mul_sum]
      apply sum_congr rfl
      intro j hj
      ring

theorem norm_iteratedDeriv_complex_square_le {s : ℝ} (hs : 0 < s) {r : ℝ}
    (hr : r ∈ Icc 0 (4 * s)) (j : ℕ) :
    ‖iteratedDeriv j (fun x : ℝ ↦ (x : ℂ) ^ 2) r‖ ≤ 16 * s ^ 2 * s⁻¹ ^ j := by
  have heq : (fun x : ℝ ↦ (x : ℂ) ^ 2) = fun x : ℝ ↦ ((x ^ 2 : ℝ) : ℂ) := by
    funext x
    simp only [Complex.ofReal_pow]
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ 2) := contDiff_id.pow 2
  rw [heq, iteratedDeriv_ofReal hsmooth]
  dsimp only
  rw [iteratedDeriv_pow, Complex.norm_real, Real.norm_eq_abs]
  by_cases hj : j ≤ 2
  · interval_cases j
    · norm_num
      nlinarith [sq_nonneg (4 * s - r), hr.1, hr.2]
    · norm_num
      rw [abs_of_nonneg hr.1]
      have heq : 16 * s ^ 2 * s⁻¹ = 16 * s := by field_simp
      rw [heq]
      linarith [hr.2]
    · norm_num
      have heq : 16 * s ^ 2 * (s ^ 2)⁻¹ = 16 := by field_simp
      rw [heq]
      norm_num
  · have hzero : (2 : ℕ).descFactorial j = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hzero]
    simp only [Nat.cast_zero, zero_mul, abs_zero]
    positivity

theorem norm_iteratedDeriv_scaled_frequencyCutoff_le {T K j : ℕ}
    (hK : 6 * T ≤ K) (hj : j ≤ 6 * T) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    ‖iteratedDeriv j (fun x : ℝ ↦ (maskedFrequencyCutoff K (x / s) : ℂ)) r‖ ≤
      (504 * (T : ℝ) ^ 2 / s) ^ j := by
  have hsmooth : ContDiff ℝ ∞ (fun x ↦ (maskedFrequencyCutoff K x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_maskedFrequencyCutoff K)
  have heq : (fun x : ℝ ↦ (maskedFrequencyCutoff K (x / s) : ℂ)) =
      fun x : ℝ ↦ (maskedFrequencyCutoff K (s⁻¹ * x) : ℂ) := by
    funext x
    congr 2
    ring
  rw [heq, iteratedDeriv_comp_const_smul
    (hsmooth.of_le (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) j))]
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hs),
    iteratedDeriv_ofReal (contDiff_maskedFrequencyCutoff K)]
  dsimp only
  rw [Complex.norm_real]
  calc
    _ ≤ s⁻¹ ^ j * (504 * (T : ℝ) ^ 2) ^ j :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedDeriv_maskedFrequencyCutoff_le_geometric hK hj _) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end FalconerThetaGauge
