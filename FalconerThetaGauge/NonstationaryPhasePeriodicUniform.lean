module

public import FalconerThetaGauge.NonstationaryPhasePeriodic

/-!
# Explicit periodic nonstationary decay

This proves the periodic form needed for circle integrals, with the same
polynomial order cost as the real-line compact-amplitude estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- Lemma 3.4 for smooth periodic lifts, with its explicit derivative base. -/
theorem nonstationary_phase_periodic {φ : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a)
    {P : ℝ} (hφP : Periodic φ P) (haP : Periodic a P) (u : ℝ)
    {A M lam Λ : ℝ} {K k : ℕ} (hreg : IsDerivativeRegular A M K a) (hk : k ≤ K)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) {U : Set ℝ} (hU : IsOpen U) (hs : tsupport a ⊆ U)
    (hlow : ∀ x ∈ U, lam ≤ ‖deriv φ x‖)
    (hhigher : ∀ j, 2 ≤ j → j ≤ k + 1 → ∀ x ∈ U, ‖iteratedDeriv j φ x‖ ≤ Λ) :
    ‖∫ x in u..u + P, Complex.exp ((φ x : ℂ) * Complex.I) * a x‖ ≤
      |P| * A * (2 * (k + 1) ^ 2 * max M (Λ / lam) / lam) ^ k := by
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
  have h := norm_intervalIntegral_oscillatoryPhase_mul_factorial_le hφ hq ha
    hφP hqP haP
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
