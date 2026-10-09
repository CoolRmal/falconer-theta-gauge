module

public import FalconerThetaGauge.NonstationaryPhasePeriodicUniform

/-! # Periodic integration by parts with the true support mass in one period -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_intervalIntegral_le_support_mass {f : ℝ → ℂ} {u P C : ℝ}
    (hP : 0 ≤ P) {S : Set ℝ} (hS : MeasurableSet S)
    (hoff : ∀ x ∉ S, f x = 0) (hbound : ∀ x, ‖f x‖ ≤ C) :
    ‖∫ x in u..u + P, f x‖ ≤ volume.real (S ∩ Ioc u (u + P)) * C := by
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hP)]
  have he : (∫ x in S, f x ∂volume.restrict (Ioc u (u + P))) =
      ∫ x, f x ∂volume.restrict (Ioc u (u + P)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hoff
  rw [← he, Measure.restrict_restrict hS]
  have hfin : volume (S ∩ Ioc u (u + P)) < (⊤ : ENNReal) :=
    (measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top
  simpa only [mul_comm] using norm_setIntegral_le_of_norm_le_const hfin
    (fun x _ ↦ hbound x)

theorem norm_intervalIntegral_oscillatoryPhase_mul_factorial_support_le
    {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    {P : ℝ} (hP : 0 ≤ P) (hφP : Periodic φ P) (hqP : Periodic q P) (haP : Periodic a P)
    (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1)
    {B A D : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D) (k : ℕ)
    (hqB : ∀ j ≤ k, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j q x‖ ≤ B * D ^ j * j.factorial)
    (haA : ∀ j ≤ k, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j a x‖ ≤ A * D ^ j * j.factorial)
    {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    ‖∫ x in u..u + P, oscillatoryPhase φ t x * a x‖ ≤
      volume.real (tsupport a ∩ Ioc u (u + P)) * A *
        (B * D * (k + 1) ^ 2 / |t|) ^ k := by
  have hfact : (k.factorial : ℝ) ≤ (k + 1) ^ k := by
    exact_mod_cast (Nat.factorial_le_pow k).trans
      (Nat.pow_le_pow_left (Nat.le_succ k) k)
  have hbound : ∀ x, ‖((nonstationaryAmplitude q)^[k] a) x‖ ≤
      A * (B * D * (k + 1) ^ 2) ^ k := by
    intro x
    have h := norm_iteratedDeriv_nonstationaryAmplitude_factorial_le hq ha
      hB hA hD k hqB haA k 0 (by omega) x
    simp only [iteratedDeriv_zero, pow_zero, mul_one, Nat.add_zero] at h
    calc
      _ ≤ (B * D * (k + 1)) ^ k * A * k.factorial := h
      _ ≤ (B * D * (k + 1)) ^ k * A * (k + 1) ^ k :=
        mul_le_mul_of_nonneg_left hfact (by positivity)
      _ = _ := by simp only [pow_two, mul_pow]; ring
  rw [intervalIntegral_oscillatoryPhase_mul_eq_iterate hφ hq ha hφP hqP haP hqφ ht u k,
    norm_mul, norm_pow, norm_neg, norm_inv, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  calc
    _ ≤ |t|⁻¹ ^ k * (volume.real (tsupport a ∩ Ioc u (u + P)) *
        (A * (B * D * (k + 1) ^ 2) ^ k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      obtain ⟨_, hs⟩ := nonstationaryAmplitude_iterate_smooth_support hq ha k
      apply norm_intervalIntegral_le_support_mass hP (isClosed_tsupport a).measurableSet
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), mul_zero]
      · intro x
        simpa only [norm_mul, norm_oscillatoryPhase, one_mul] using hbound x
    _ = _ := by simp only [div_eq_mul_inv, mul_pow]; ring


theorem nonstationary_phase_periodic_support {φ : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a)
    {P : ℝ} (hP : 0 ≤ P) (hφP : Periodic φ P) (haP : Periodic a P) (u : ℝ)
    {A M lam Λ : ℝ} {K k : ℕ} (hreg : IsDerivativeRegular A M K a) (hk : k ≤ K)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) {U : Set ℝ} (hU : IsOpen U) (hs : tsupport a ⊆ U)
    (hlow : ∀ x ∈ U, lam ≤ ‖deriv φ x‖)
    (hhigher : ∀ j, 2 ≤ j → j ≤ k + 1 → ∀ x ∈ U, ‖iteratedDeriv j φ x‖ ≤ Λ) :
    ‖∫ x in u..u + P, Complex.exp ((φ x : ℂ) * Complex.I) * a x‖ ≤
      volume.real (tsupport a ∩ Ioc u (u + P)) * A *
        (2 * (k + 1) ^ 2 * max M (Λ / lam) / lam) ^ k := by
  let q := nonstationaryReciprocal φ lam
  let D := 2 * max M (Λ / lam)
  have hq : ContDiff ℝ ∞ q := contDiff_nonstationaryReciprocal hφ lam
  have hD : 0 ≤ D := by dsimp [D]; linarith [le_max_left M (Λ / lam), hreg.one_le_scale]
  have hM : 0 ≤ M := by linarith [hreg.one_le_scale]
  have hscale : M ≤ D := by
    dsimp [D]
    linarith [le_max_left M (Λ / lam), hreg.one_le_scale]
  have hratio : 1 + Λ / lam ≤ D := by
    dsimp [D]
    linarith [le_max_left M (Λ / lam), le_max_right M (Λ / lam), hreg.one_le_scale]
  have hrecip := norm_iteratedDeriv_reciprocal_le
    (contDiff_infty_iff_deriv.mp hφ).2 hq hU
    (fun x hx ↦ nonstationaryReciprocal_mul_deriv hlam (hlow x hx)) hlam hΛ hlow k
    (fun j hj hjk x hx ↦ by
      have h := hhigher (j + 1) (by omega) (by omega) x hx
      simpa only [iteratedDeriv_succ'] using h)
  have hqB : ∀ j ≤ k, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j q x‖ ≤ lam⁻¹ * D ^ j * j.factorial := by
    intro j hj x hx
    exact (hrecip j hj x (hs hx)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Λ / lam) hratio j) (by positivity))
        (Nat.cast_nonneg _))
  have haA : ∀ j ≤ k, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j a x‖ ≤ A * D ^ j * j.factorial := by
    intro j hj x _
    have hfact : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
    calc
      _ ≤ A * M ^ j := hreg.bound j (hj.trans hk) x
      _ ≤ A * D ^ j := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hM hscale j) hreg.amplitude_nonneg
      _ ≤ _ := by nlinarith [mul_nonneg hreg.amplitude_nonneg (pow_nonneg hD j)]
  have hqP : Periodic q P := by
    intro x
    change lam⁻¹ * regularizedReciprocal (lam⁻¹ * deriv φ (x + P)) =
      lam⁻¹ * regularizedReciprocal (lam⁻¹ * deriv φ x)
    rw [periodic_deriv hφP x]
  have h := norm_intervalIntegral_oscillatoryPhase_mul_factorial_support_le hφ hq ha
    hP hφP hqP haP
    (fun x hx ↦ nonstationaryReciprocal_mul_deriv hlam (hlow x (hs hx)))
    (by positivity : 0 ≤ lam⁻¹) hreg.amplitude_nonneg hD k hqB haA (by norm_num : (1 : ℝ) ≠ 0) u
  have hbase : lam⁻¹ * D * (k + 1) ^ 2 / |(1 : ℝ)| =
      2 * (k + 1) ^ 2 * max M (Λ / lam) / lam := by
    dsimp [D]
    simp only [abs_one, div_eq_mul_inv]
    ring
  rw [hbase] at h
  simpa only [oscillatoryPhase, Complex.ofReal_one, one_mul] using h


end FalconerThetaGauge
