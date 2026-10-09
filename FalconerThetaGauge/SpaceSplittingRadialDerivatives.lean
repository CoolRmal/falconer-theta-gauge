module

public import FalconerThetaGauge.SpaceSplittingRadialPower

/-! # The literal first two radial derivative estimates in source Estimate 7.8 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_scaled_cutoff_le_exact {K j : ℕ} (hj : j ≤ K)
    {s : ℝ} (hs : 0 < s) (r : ℝ) :
    ‖iteratedDeriv j (fun x : ℝ ↦ (maskedFrequencyCutoff K (x / s) : ℂ)) r‖ ≤
      (14 : ℝ) ^ j * (j.factorial : ℝ) ^ 2 / s ^ j := by
  have hf : ContDiff ℝ ∞ (fun x ↦ (maskedFrequencyCutoff K x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_maskedFrequencyCutoff K)
  have heq : (fun x : ℝ ↦ (maskedFrequencyCutoff K (x / s) : ℂ)) =
      fun x : ℝ ↦ (maskedFrequencyCutoff K (s⁻¹ * x) : ℂ) := by
    funext x
    congr 2
    ring
  rw [heq, iteratedDeriv_comp_const_smul
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) j))]
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hs),
    iteratedDeriv_ofReal (contDiff_maskedFrequencyCutoff K), Complex.norm_real]
  calc
    _ ≤ s⁻¹ ^ j * ((14 : ℝ) ^ j * (j.factorial : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_iteratedDeriv_maskedFrequencyCutoff_le K j hj _)
        (by positivity)
    _ = _ := by rw [inv_pow]; ring

theorem norm_iteratedDeriv_two_mul_le {f g : ℝ → ℂ} {r : ℝ}
    (hf : ContDiffAt ℝ 2 f r) (hg : ContDiffAt ℝ 2 g r) :
    ‖iteratedDeriv 2 (f * g) r‖ ≤
      ‖iteratedDeriv 0 f r‖ * ‖iteratedDeriv 2 g r‖ +
        2 * ‖iteratedDeriv 1 f r‖ * ‖iteratedDeriv 1 g r‖ +
        ‖iteratedDeriv 2 f r‖ * ‖iteratedDeriv 0 g r‖ := by
  rw [iteratedDeriv_mul hf hg]
  have h := norm_sum_le (Finset.range (2 + 1))
    (fun j ↦ (Nat.choose 2 j : ℂ) * iteratedDeriv j f r * iteratedDeriv (2 - j) g r)
  simpa [Finset.sum_range_succ, norm_mul] using h

theorem norm_deriv_ofReal_zpow (m : ℤ) {r : ℝ} (hr : 0 < r) :
    ‖iteratedDeriv 1 (fun x : ℝ ↦ ((x ^ m : ℝ) : ℂ)) r‖ = |(m : ℝ)| * r ^ m / r := by
  rw [iteratedDeriv_ofReal_zpow m 1 hr.ne']
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, sub_zero,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Nat.cast_one]
  rw [zpow_sub₀ hr.ne', zpow_one, abs_div, abs_of_pos (zpow_pos hr m), abs_of_pos hr]
  ring

theorem norm_secondDeriv_ofReal_zpow_le (m : ℤ) {r : ℝ} (hr : 0 < r) :
    ‖iteratedDeriv 2 (fun x : ℝ ↦ ((x ^ m : ℝ) : ℂ)) r‖ ≤
      |(m : ℝ)| * (|(m : ℝ)| + 1) * r ^ m / r ^ 2 := by
  rw [iteratedDeriv_ofReal_zpow m 2 hr.ne']
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
    sub_zero, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  rw [zpow_sub₀ hr.ne', zpow_natCast, abs_div, abs_of_pos (zpow_pos hr m),
    abs_of_pos (pow_pos hr 2)]
  have ha : |(m : ℝ) - 1| ≤ |(m : ℝ)| + 1 := by
    simpa only [sub_zero, zero_sub, abs_neg, abs_one] using abs_sub_le (m : ℝ) 0 1
  have h := mul_le_mul_of_nonneg_left ha (abs_nonneg (m : ℝ))
  convert mul_le_mul_of_nonneg_right h (div_nonneg (zpow_nonneg hr.le m) (sq_nonneg r))
    using 1
  ring


/-- The explicit source amplitude bound for `rᵐ` on the true dyadic window. -/
def spaceSplittingRadialBound (v : ℕ) (m : ℤ) : ℝ :=
  (4 : ℝ) ^ m.natAbs * ((2 : ℝ) ^ v) ^ m

theorem spaceSplittingRadialBound_pos (v : ℕ) (m : ℤ) :
    0 < spaceSplittingRadialBound v m := by
  unfold spaceSplittingRadialBound
  positivity

/-- The actual cutoff-power product has the source `784(|m|+1)²` second derivative bound. -/
theorem norm_secondDeriv_cutoff_zpow_le {K : ℕ} (hK : 2 ≤ K) {s r : ℝ}
    (hs : 0 < s) (hr : r ∈ Icc (s / 4) (4 * s)) (m : ℤ) :
    ‖iteratedDeriv 2 ((fun x : ℝ ↦ (maskedFrequencyCutoff K (x / s) : ℂ)) *
      (fun x : ℝ ↦ ((x ^ m : ℝ) : ℂ))) r‖ ≤
        ((4 : ℝ) ^ m.natAbs * s ^ m) * 784 * (|(m : ℝ)| + 1) ^ 2 / s ^ 2 := by
  let f : ℝ → ℂ := fun x ↦ (maskedFrequencyCutoff K (x / s) : ℂ)
  let g : ℝ → ℂ := fun x ↦ ((x ^ m : ℝ) : ℂ)
  let a : ℝ := |(m : ℝ)|
  let q : ℝ := r ^ m
  have hrpos : 0 < r := (by positivity : (0 : ℝ) < s / 4).trans_le hr.1
  have ha : 0 ≤ a := abs_nonneg _
  have hq : 0 ≤ q := zpow_nonneg hrpos.le m
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp
    ((contDiff_maskedFrequencyCutoff K).comp (contDiff_id.div_const s))
  have hg : ContDiffAt ℝ 2 g r := (Complex.ofRealCLM.contDiff.contDiffAt.comp r
    (contDiffAt_real_zpow m hrpos.ne')).of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞)
  have h := norm_iteratedDeriv_two_mul_le (hf.of_le (by simp)).contDiffAt hg
  have hf₀ : ‖iteratedDeriv 0 f r‖ ≤ 1 := by
    simpa only [iteratedDeriv_zero, f, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (maskedFrequencyCutoff_mem_Icc K _).1] using
        (maskedFrequencyCutoff_mem_Icc K (r / s)).2
  have hf₁ : ‖iteratedDeriv 1 f r‖ ≤ 14 / s := by
    have hh := norm_iteratedDeriv_scaled_cutoff_le_exact (K := K) (by omega : 1 ≤ K) hs r
    simpa only [f, pow_one, Nat.factorial_one, Nat.cast_one, one_pow, mul_one] using hh
  have hf₂ : ‖iteratedDeriv 2 f r‖ ≤ 784 / s ^ 2 := by
    have hh := norm_iteratedDeriv_scaled_cutoff_le_exact (K := K) hK hs r
    norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_two] at hh
    convert hh using 1
    norm_num [f, pow_two]
  have hir : r⁻¹ ≤ 4 / s := by
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < s / 4) hr.1
    simpa only [one_div, inv_div, inv_inv] using hh
  have hg₀ : ‖iteratedDeriv 0 g r‖ = q := by
    simp only [iteratedDeriv_zero, g, q, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zpow_pos hrpos m)]
  have hg₁ : ‖iteratedDeriv 1 g r‖ ≤ (4 * a / s) * q := by
    rw [show g = (fun x : ℝ ↦ ((x ^ m : ℝ) : ℂ)) from rfl,
      norm_deriv_ofReal_zpow m hrpos]
    convert mul_le_mul_of_nonneg_left hir (mul_nonneg ha hq) using 1 <;> dsimp [a, q] <;> ring
  have hg₂ : ‖iteratedDeriv 2 g r‖ ≤ (16 * a * (a + 1) / s ^ 2) * q := by
    apply (norm_secondDeriv_ofReal_zpow_le m hrpos).trans
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hrpos.le) hir 2
    have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg ha
      (by linarith : 0 ≤ a + 1)) hq)
    convert hmul using 1 <;> dsimp [a, q] <;> simp only [div_pow, inv_pow] <;> ring
  have hprod : ‖iteratedDeriv 2 (f * g) r‖ ≤
      q / s ^ 2 * (784 + 112 * a + 16 * a * (a + 1)) := by
    apply h.trans
    rw [hg₀]
    calc
      _ ≤ 1 * ((16 * a * (a + 1) / s ^ 2) * q) +
          2 * (14 / s) * ((4 * a / s) * q) + (784 / s ^ 2) * q := by
        apply add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul hf₀ hg₂ (norm_nonneg _) (by norm_num)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hf₁ (by norm_num)) hg₁
            (norm_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_right hf₂ hq
      _ = _ := by ring
  apply hprod.trans
  calc
    _ ≤ q / s ^ 2 * (784 * (a + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (div_nonneg hq (sq_nonneg s))
    _ ≤ ((4 : ℝ) ^ m.natAbs * s ^ m) / s ^ 2 * (784 * (a + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (real_zpow_le_dyadic_window hs hr m) (sq_nonneg s)) (by positivity)
    _ = _ := by dsimp [a]; ring

theorem norm_spaceSplittingRadialAmplitude_le_on_support (K v : ℕ) (m : ℤ) {r : ℝ}
    (hr : r ∈ tsupport (spaceSplittingRadialAmplitude K v m)) :
    ‖spaceSplittingRadialAmplitude K v m r‖ ≤
      spaceSplittingRadialBound v m / (2 : ℝ) ^ v := by
  have hs : (0 : ℝ) < 2 ^ v := by positivity
  have hwindow := tsupport_spaceSplittingRadialAmplitude_subset K v m hr
  have hrpos : 0 < r := (by positivity : (0 : ℝ) < 2 ^ v / 4).trans_le hwindow.1
  simp only [spaceSplittingRadialAmplitude, norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num,
    abs_of_nonneg (maskedFrequencyCutoff_mem_Icc K _).1, abs_of_pos (zpow_pos hrpos m)]
  calc
    _ ≤ ((2 : ℝ) ^ v)⁻¹ * 1 * spaceSplittingRadialBound v m :=
      mul_le_mul (mul_le_mul_of_nonneg_left (maskedFrequencyCutoff_mem_Icc K _).2
        (by positivity)) (real_zpow_le_dyadic_window hs hwindow m)
        (zpow_nonneg hrpos.le m) (by positivity)
    _ = _ := by ring

theorem norm_secondDeriv_spaceSplittingRadialAmplitude_le_on_support {K v : ℕ}
    (hK : 2 ≤ K) (m : ℤ) {r : ℝ}
    (hr : r ∈ tsupport (spaceSplittingRadialAmplitude K v m)) :
    ‖iteratedDeriv 2 (spaceSplittingRadialAmplitude K v m) r‖ ≤
      (spaceSplittingRadialBound v m / (2 : ℝ) ^ v) *
        (28 * (|(m : ℝ)| + 1) / (2 : ℝ) ^ v) ^ 2 := by
  have hs : (0 : ℝ) < 2 ^ v := by positivity
  have h := norm_secondDeriv_cutoff_zpow_le hK hs
    (tsupport_spaceSplittingRadialAmplitude_subset K v m hr) m
  have heq : spaceSplittingRadialAmplitude K v m = fun x ↦ (((2 : ℝ) ^ v)⁻¹ : ℂ) *
      ((fun x : ℝ ↦ (maskedFrequencyCutoff K (x / (2 : ℝ) ^ v) : ℂ)) *
        (fun x : ℝ ↦ ((x ^ m : ℝ) : ℂ))) x := by
    funext x
    dsimp [spaceSplittingRadialAmplitude]
    ring
  rw [heq, iteratedDeriv_const_mul_field, norm_mul, norm_inv]
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num]
  convert mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le) using 1
  unfold spaceSplittingRadialBound
  ring

theorem volume_tsupport_spaceSplittingRadialAmplitude_le (K v : ℕ) (m : ℤ) :
    volume.real (tsupport (spaceSplittingRadialAmplitude K v m)) ≤ 4 * (2 : ℝ) ^ v := by
  have hs : (0 : ℝ) < 2 ^ v := by positivity
  have h := measureReal_mono (μ := volume)
    (tsupport_spaceSplittingRadialAmplitude_subset K v m) isCompact_Icc.measure_ne_top
  rw [Real.volume_real_Icc_of_le (by linarith : (2 : ℝ) ^ v / 4 ≤ 4 * (2 : ℝ) ^ v)] at h
  exact h.trans (by linarith)


end FalconerThetaGauge
