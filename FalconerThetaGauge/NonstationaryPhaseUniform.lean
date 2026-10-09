module

public import FalconerThetaGauge.RegularizedReciprocal

/-!
# Explicit nonstationary decay for smooth compact amplitudes

The smooth reciprocal is used only to make a globally defined transport
operator. Its derivative constants on the support follow from the actual
reciprocal identity, so its arbitrary cutoff region contributes no cost.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace FalconerThetaGauge

/-- A globally smooth reciprocal of the phase derivative on its nonstationary region. -/
def nonstationaryReciprocal (φ : ℝ → ℝ) (lam : ℝ) (x : ℝ) : ℝ :=
  lam⁻¹ * regularizedReciprocal (lam⁻¹ * deriv φ x)

theorem contDiff_nonstationaryReciprocal {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (lam : ℝ) :
    ContDiff ℝ ∞ (nonstationaryReciprocal φ lam) := by
  have hder := (contDiff_infty_iff_deriv.mp hφ).2
  exact contDiff_const.mul (contDiff_regularizedReciprocal.comp (contDiff_const.mul hder))

theorem nonstationaryReciprocal_mul_deriv {φ : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ} (hx : lam ≤ ‖deriv φ x‖) :
    nonstationaryReciprocal φ lam x * deriv φ x = 1 := by
  have hnorm : 1 ≤ |lam⁻¹ * deriv φ x| := by
    rw [abs_mul, abs_inv, abs_of_pos hlam]
    have h : 1 ≤ ‖deriv φ x‖ / lam := (le_div_iff₀ hlam).mpr (by simpa using hx)
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using h
  have hne : deriv φ x ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero] at hx
    exact (not_le_of_gt hlam) hx
  rw [nonstationaryReciprocal, regularizedReciprocal_eq_inv hnorm]
  field_simp

/-- The real-line form of Lemma 3.4, with exactly its polynomial derivative base. -/
theorem nonstationary_phase {φ : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    {A M lam Λ : ℝ} {K k : ℕ} (hreg : IsDerivativeRegular A M K a) (hk : k ≤ K)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) {U : Set ℝ} (hU : IsOpen U) (hs : tsupport a ⊆ U)
    (hlow : ∀ x ∈ U, lam ≤ ‖deriv φ x‖)
    (hhigher : ∀ j, 2 ≤ j → j ≤ k + 1 → ∀ x ∈ U, ‖iteratedDeriv j φ x‖ ≤ Λ) :
    ‖∫ x, Complex.exp ((φ x : ℂ) * Complex.I) * a x‖ ≤
      volume.real (tsupport a) * A *
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
  have h := norm_integral_oscillatoryPhase_mul_factorial_le hφ hq ha hac
    (fun x hx ↦ nonstationaryReciprocal_mul_deriv hlam (hlow x (hs hx)))
    (by positivity : 0 ≤ lam⁻¹) hreg.amplitude_nonneg hD k hqB haA (by norm_num : (1 : ℝ) ≠ 0)
  have hbase : lam⁻¹ * D * (k + 1) ^ 2 / |(1 : ℝ)| =
      2 * (k + 1) ^ 2 * max M (Λ / lam) / lam := by
    dsimp [D]
    simp only [abs_one, div_eq_mul_inv]
    ring
  rw [hbase] at h
  simpa only [oscillatoryPhase, Complex.ofReal_one, one_mul] using h

end FalconerThetaGauge
