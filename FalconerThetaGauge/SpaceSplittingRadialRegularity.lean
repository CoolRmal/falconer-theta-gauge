module

public import FalconerThetaGauge.SpaceSplittingRadialDerivatives

/-! # All genuine integer-power radial derivatives in the equal-sign terms -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_mul_le_contDiffAt {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) {A B M P : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (k : ℕ)
    (hfb : ∀ j ≤ k, ‖iteratedDeriv j f x‖ ≤ A * M ^ j)
    (hgb : ∀ j ≤ k, ‖iteratedDeriv j g x‖ ≤ B * P ^ j) :
    ‖iteratedDeriv k (f * g) x‖ ≤ (A * B) * (M + P) ^ k := by
  have hle := ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) k
  rw [iteratedDeriv_mul (hf.of_le hle) (hg.of_le hle)]
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
      intro j _
      ring

theorem norm_iteratedDeriv_ofReal_zpow_le_scale {T j : ℕ} (hj : j ≤ 6 * T)
    {m : ℤ} (hm : |(m : ℝ)| ≤ 2 * T) {s r : ℝ} (hs : 0 < s)
    (hr : r ∈ Icc (s / 4) (4 * s)) :
    ‖iteratedDeriv j (fun x : ℝ ↦ ((x ^ m : ℝ) : ℂ)) r‖ ≤
      ((4 : ℝ) ^ m.natAbs * s ^ m) * (32 * T / s) ^ j := by
  have hrpos : 0 < r := (by positivity : 0 < s / 4).trans_le hr.1
  have hcoeff : |∏ k ∈ range j, ((m : ℝ) - k)| ≤ (8 * T) ^ j := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _k ∈ range j, (8 * (T : ℝ)) := by
        apply prod_le_prod₀ (by intros; positivity)
        intro k hk
        have hk' : (k : ℝ) ≤ 6 * T := by
          exact_mod_cast (le_trans (mem_range.1 hk).le hj)
        have habs : |(m : ℝ) - k| ≤ |(m : ℝ)| + k := by
          simpa only [sub_zero, zero_sub, abs_neg, Nat.abs_cast] using
            abs_sub_le (m : ℝ) 0 k
        linarith
      _ = _ := by simp
  rw [iteratedDeriv_ofReal_zpow m j hrpos.ne', Complex.norm_real, Real.norm_eq_abs,
    abs_mul, zpow_sub₀ hrpos.ne', abs_div, abs_of_pos (zpow_pos hrpos _),
    abs_of_pos (zpow_pos hrpos _), zpow_natCast]
  calc
    _ ≤ (8 * T) ^ j * (r ^ m / r ^ j) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = r ^ m * (8 * T / r) ^ j := by rw [div_pow]; ring
    _ ≤ ((4 : ℝ) ^ m.natAbs * s ^ m) * (32 * T / s) ^ j := by
      apply mul_le_mul (real_zpow_le_dyadic_window hs hr m) _ (by positivity) (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_iff₀ hrpos).2
      have heq : (32 * (T : ℝ) / s) * (s / 4) = 8 * T := by field_simp; ring
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hr.1 (by positivity)

theorem norm_iteratedDeriv_spaceSplittingRadialAmplitude_le {T K v j : ℕ}
    (hT : 1 ≤ T) (hK : 6 * T ≤ K) (hj : j ≤ 6 * T) {m : ℤ}
    (hm : |(m : ℝ)| ≤ 2 * T) {r : ℝ}
    (hr : r ∈ tsupport (spaceSplittingRadialAmplitude K v m)) :
    ‖iteratedDeriv j (spaceSplittingRadialAmplitude K v m) r‖ ≤
      (spaceSplittingRadialBound v m / (2 : ℝ) ^ v) *
        (600 * (T : ℝ) ^ 2 / (2 : ℝ) ^ v) ^ j := by
  let s : ℝ := (2 : ℝ) ^ v
  have hs : 0 < s := by dsimp [s]; positivity
  have hr' : r ∈ Icc (s / 4) (4 * s) :=
    tsupport_spaceSplittingRadialAmplitude_subset K v m hr
  have hrpos : 0 < r := (by positivity : 0 < s / 4).trans_le hr'.1
  let f : ℝ → ℂ := fun x ↦ (maskedFrequencyCutoff K (x / s) : ℂ)
  let g : ℝ → ℂ := fun x ↦ ((x ^ m : ℝ) : ℂ)
  have hf : ContDiffAt ℝ ∞ f r := (Complex.ofRealCLM.contDiff.comp
    ((contDiff_maskedFrequencyCutoff K).comp (contDiff_id.div_const s))).contDiffAt
  have hg : ContDiffAt ℝ ∞ g r := Complex.ofRealCLM.contDiff.contDiffAt.comp r
    (contDiffAt_real_zpow m hrpos.ne')
  have hprod := norm_iteratedDeriv_mul_le_contDiffAt (A := 1)
    (B := spaceSplittingRadialBound v m) hf hg (by norm_num)
    (by positivity : 0 ≤ 504 * (T : ℝ) ^ 2 / s) j
    (fun l hl ↦ by simpa only [one_mul] using
      norm_iteratedDeriv_scaled_frequencyCutoff_le hK (hl.trans hj) hs r)
    (fun l hl ↦ norm_iteratedDeriv_ofReal_zpow_le_scale (hl.trans hj) hm hs hr')
  have heq : spaceSplittingRadialAmplitude K v m =
      fun x ↦ ((s⁻¹ : ℝ) : ℂ) * (f * g) x := by
    funext x
    dsimp only [spaceSplittingRadialAmplitude, s, f, g, Pi.mul_apply]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow]
    ring
  rw [heq, iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  calc
    _ ≤ s⁻¹ * ((1 * spaceSplittingRadialBound v m) *
        (504 * (T : ℝ) ^ 2 / s + 32 * T / s) ^ j) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ s⁻¹ * (spaceSplittingRadialBound v m * (600 * (T : ℝ) ^ 2 / s) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [one_mul]
      apply mul_le_mul_of_nonneg_left _ (spaceSplittingRadialBound_pos v m).le
      apply pow_le_pow_left₀ (by positivity)
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hs.le
      have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith
    _ = _ := by change _ = (spaceSplittingRadialBound v m / s) * _; ring

end FalconerThetaGauge
