module

public import FalconerThetaGauge.NonstationaryPhaseUniform
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Nonstationary integration by parts over a period

The endpoint terms cancel for genuine periodic amplitudes and phases. The
same transported amplitudes and their local support derivative bounds are
therefore available for the circle integrals used in the energy estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem periodic_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {P : ℝ} (hf : Periodic f P) : Periodic (deriv f) P := by
  intro x
  rw [← deriv_comp_add_const, hf.funext]

theorem periodic_nonstationaryAmplitude {q : ℝ → ℝ} {a : ℝ → ℂ} {P : ℝ}
    (hq : Periodic q P) (ha : Periodic a P) :
    Periodic (nonstationaryAmplitude q a) P := by
  apply periodic_deriv
  intro x
  change (q (x + P) : ℂ) * a (x + P) = (q x : ℂ) * a x
  rw [hq x, ha x]

theorem periodic_nonstationaryAmplitude_iterate {q : ℝ → ℝ} {a : ℝ → ℂ} {P : ℝ}
    (hq : Periodic q P) (ha : Periodic a P) (k : ℕ) :
    Periodic ((nonstationaryAmplitude q)^[k] a) P := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact periodic_nonstationaryAmplitude hq ih

/-- The actual boundary cancellation over a period. -/
theorem intervalIntegral_oscillatoryPhase_mul_amplitude {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    {P : ℝ} (hφP : Periodic φ P) (hqP : Periodic q P) (haP : Periodic a P)
    (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1) (t u : ℝ) :
    (∫ x in u..u + P, oscillatoryPhase φ t x * nonstationaryAmplitude q a x) =
      -((t : ℂ) * Complex.I * ∫ x in u..u + P, oscillatoryPhase φ t x * a x) := by
  have hqa : ContDiff ℝ ∞ (fun x ↦ (q x : ℂ) * a x) :=
    (Complex.ofRealCLM.contDiff.comp hq).mul ha
  have hph := contDiff_oscillatoryPhase hφ t
  have hder : Continuous (fun x ↦ oscillatoryPhase φ t x *
      ((t : ℂ) * ((deriv φ x : ℝ) : ℂ) * Complex.I)) :=
    hph.continuous.mul ((Complex.continuous_ofReal.comp
      (hφ.continuous_deriv (by simp))).const_mul _ |>.mul_const _)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := u) (b := u + P)
    (fun x _ ↦ hasDerivAt_oscillatoryPhase hφ t x)
    (fun x _ ↦ (hqa.differentiable (by simp) x).hasDerivAt)
    (hder.intervalIntegrable u (u + P))
    ((contDiff_nonstationaryAmplitude hq ha).continuous.intervalIntegrable u (u + P))
  have hed :
      (∫ x in u..u + P, (oscillatoryPhase φ t x *
        ((t : ℂ) * ((deriv φ x : ℝ) : ℂ) * Complex.I)) * ((q x : ℂ) * a x)) =
      (t : ℂ) * Complex.I * ∫ x in u..u + P, oscillatoryPhase φ t x * a x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    by_cases hax : a x = 0
    · simp [hax]
    · have hqφx : (q x : ℂ) * ((deriv φ x : ℝ) : ℂ) = 1 := by
        exact_mod_cast hqφ x (subset_tsupport a hax)
      calc
        _ = ((t : ℂ) * Complex.I) * (oscillatoryPhase φ t x * a x) *
            ((q x : ℂ) * ((deriv φ x : ℝ) : ℂ)) := by ring
        _ = _ := by rw [hqφx, mul_one]
  rw [hed] at hibp
  simpa only [oscillatoryPhase, nonstationaryAmplitude, hφP u, hqP u, haP u,
    sub_self, zero_sub] using hibp

/-- Exact repeated integration by parts on a full period. -/
theorem intervalIntegral_oscillatoryPhase_mul_eq_iterate
    {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    {P : ℝ} (hφP : Periodic φ P) (hqP : Periodic q P) (haP : Periodic a P)
    (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1) {t : ℝ} (ht : t ≠ 0)
    (u : ℝ) (k : ℕ) :
    (∫ x in u..u + P, oscillatoryPhase φ t x * a x) =
      (-((t : ℂ) * Complex.I)⁻¹) ^ k *
        ∫ x in u..u + P, oscillatoryPhase φ t x * ((nonstationaryAmplitude q)^[k] a) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hka, hks⟩ := nonstationaryAmplitude_iterate_smooth_support hq ha k
    have hkp := periodic_nonstationaryAmplitude_iterate hqP haP k
    have hident := intervalIntegral_oscillatoryPhase_mul_amplitude hφ hq hka
      hφP hqP hkp (fun x hx ↦ hqφ x (hks hx)) t u
    have hone : (∫ x in u..u + P, oscillatoryPhase φ t x *
        ((nonstationaryAmplitude q)^[k] a) x) =
        -((t : ℂ) * Complex.I)⁻¹ * ∫ x in u..u + P,
          oscillatoryPhase φ t x *
            nonstationaryAmplitude q ((nonstationaryAmplitude q)^[k] a) x := by
      rw [hident]
      field_simp [Complex.ofReal_ne_zero.mpr ht]
    rw [ih, hone, pow_succ, Function.iterate_succ_apply', mul_assoc]

/-- Uniform periodic decay from the literal factorial derivative bounds. -/
theorem norm_intervalIntegral_oscillatoryPhase_mul_factorial_le
    {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    {P : ℝ} (hφP : Periodic φ P) (hqP : Periodic q P) (haP : Periodic a P)
    (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1)
    {B A D : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D) (k : ℕ)
    (hqB : ∀ j ≤ k, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j q x‖ ≤ B * D ^ j * j.factorial)
    (haA : ∀ j ≤ k, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j a x‖ ≤ A * D ^ j * j.factorial)
    {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    ‖∫ x in u..u + P, oscillatoryPhase φ t x * a x‖ ≤
      |P| * A * (B * D * (k + 1) ^ 2 / |t|) ^ k := by
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
    _ ≤ |t|⁻¹ ^ k * (A * (B * D * (k + 1) ^ 2) ^ k * |(u + P) - u|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _
      simpa only [norm_mul, norm_oscillatoryPhase, one_mul] using hbound x
    _ = _ := by simp only [add_sub_cancel_left, div_eq_mul_inv, mul_pow]; ring

end FalconerThetaGauge
