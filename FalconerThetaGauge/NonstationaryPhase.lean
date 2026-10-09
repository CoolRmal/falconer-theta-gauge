/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the falconer-packing development; see docs/ATTRIBUTION.md.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Repeated integration by parts for a nonstationary phase

The inverse derivative of the phase is required only on the amplitude's closed support.
The transformed amplitudes have smaller supports, so the same local hypothesis suffices
at every iteration. Compact support supplies all integrability and boundary conditions.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The amplitude transformation used in nonstationary integration by parts. -/
noncomputable def nonstationaryAmplitude (q : ℝ → ℝ) (a : ℝ → ℂ) : ℝ → ℂ :=
  deriv (fun x ↦ (q x : ℂ) * a x)

/-- Integration by parts does not enlarge the closed support of the amplitude. -/
theorem tsupport_nonstationaryAmplitude_subset (q : ℝ → ℝ) (a : ℝ → ℂ) :
    tsupport (nonstationaryAmplitude q a) ⊆ tsupport a :=
  tsupport_deriv_subset.trans tsupport_mul_subset_right

theorem hasCompactSupport_nonstationaryAmplitude (q : ℝ → ℝ) {a : ℝ → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (nonstationaryAmplitude q a) :=
  ha.mul_left.deriv

theorem contDiff_nonstationaryAmplitude {q : ℝ → ℝ} {a : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (nonstationaryAmplitude q a) :=
  (contDiff_infty_iff_deriv.mp ((Complex.ofRealCLM.contDiff.comp hq).mul ha)).2

/-- Smoothness and support shrinkage also hold for periodic, noncompact amplitudes. -/
theorem nonstationaryAmplitude_iterate_smooth_support {q : ℝ → ℝ} {a : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a) (N : ℕ) :
    ContDiff ℝ ∞ ((nonstationaryAmplitude q)^[N] a) ∧
      tsupport ((nonstationaryAmplitude q)^[N] a) ⊆ tsupport a := by
  induction N with
  | zero => exact ⟨ha, Subset.rfl⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨contDiff_nonstationaryAmplitude hq ih.1,
      (tsupport_nonstationaryAmplitude_subset q _).trans ih.2⟩

/-- Every iterated amplitude remains smooth and supported inside the original compact set. -/
theorem nonstationaryAmplitude_iterate_properties {q : ℝ → ℝ} {a : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (N : ℕ) :
    ContDiff ℝ ∞ ((nonstationaryAmplitude q)^[N] a) ∧
      HasCompactSupport ((nonstationaryAmplitude q)^[N] a) ∧
      tsupport ((nonstationaryAmplitude q)^[N] a) ⊆ tsupport a := by
  induction N with
  | zero => exact ⟨ha, hac, Subset.rfl⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨contDiff_nonstationaryAmplitude hq ih.1,
      hasCompactSupport_nonstationaryAmplitude q ih.2.1,
      (tsupport_nonstationaryAmplitude_subset q _).trans ih.2.2⟩

/-- The complex exponential associated with a real phase and frequency. -/
noncomputable def oscillatoryPhase (φ : ℝ → ℝ) (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * (φ x : ℂ) * Complex.I)

@[simp] theorem norm_oscillatoryPhase (φ : ℝ → ℝ) (t x : ℝ) :
    ‖oscillatoryPhase φ t x‖ = 1 := by
  simpa only [oscillatoryPhase, Complex.ofReal_mul] using
    Complex.norm_exp_ofReal_mul_I (t * φ x)

theorem contDiff_oscillatoryPhase {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    ContDiff ℝ ∞ (oscillatoryPhase φ t) :=
  ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ)).mul contDiff_const).cexp

theorem hasDerivAt_oscillatoryPhase {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (oscillatoryPhase φ t)
      (oscillatoryPhase φ t x * ((t : ℂ) * ((deriv φ x : ℝ) : ℂ) * Complex.I)) x := by
  exact ((((hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp).const_mul
    (t : ℂ)).mul_const Complex.I).cexp

/-- The oscillatory integral is an ordinary, absolutely convergent Bochner integral. -/
theorem integrable_oscillatoryPhase_mul {φ : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (t : ℝ) :
    Integrable (fun x ↦ oscillatoryPhase φ t x * a x) :=
  ((contDiff_oscillatoryPhase hφ t).continuous.mul
    ha.continuous).integrable_of_hasCompactSupport hac.mul_left

/-- One integration-by-parts identity, before division by the frequency. -/
theorem integral_oscillatoryPhase_mul_amplitude {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1) (t : ℝ) :
    (∫ x, oscillatoryPhase φ t x * nonstationaryAmplitude q a x) =
      -((t : ℂ) * Complex.I * ∫ x, oscillatoryPhase φ t x * a x) := by
  have hqa : ContDiff ℝ ∞ (fun x ↦ (q x : ℂ) * a x) :=
    (Complex.ofRealCLM.contDiff.comp hq).mul ha
  have hph := contDiff_oscillatoryPhase hφ t
  have hder : Continuous (fun x ↦ oscillatoryPhase φ t x *
      ((t : ℂ) * ((deriv φ x : ℝ) : ℂ) * Complex.I)) :=
    hph.continuous.mul ((Complex.continuous_ofReal.comp
      (hφ.continuous_deriv (by simp))).const_mul _ |>.mul_const _)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := oscillatoryPhase φ t) (v := fun x ↦ (q x : ℂ) * a x)
    (u' := fun x ↦ oscillatoryPhase φ t x *
      ((t : ℂ) * ((deriv φ x : ℝ) : ℂ) * Complex.I))
    (v' := nonstationaryAmplitude q a)
    (fun x _ ↦ hasDerivAt_oscillatoryPhase hφ t x)
    (fun x _ ↦ (hqa.differentiable (by simp) x).hasDerivAt)
    (integrable_oscillatoryPhase_mul hφ (contDiff_nonstationaryAmplitude hq ha)
      (hasCompactSupport_nonstationaryAmplitude q hac) t)
    ((hder.mul hqa.continuous).integrable_of_hasCompactSupport hac.mul_left.mul_left)
    ((hph.continuous.mul hqa.continuous).integrable_of_hasCompactSupport
      hac.mul_left.mul_left)
  rw [hibp]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hax : a x = 0
  · simp [hax]
  · have hqφx : (q x : ℂ) * ((deriv φ x : ℝ) : ℂ) = 1 := by
      exact_mod_cast hqφ x (subset_tsupport a hax)
    calc
      _ = ((t : ℂ) * Complex.I) * (oscillatoryPhase φ t x * a x) *
          ((q x : ℂ) * ((deriv φ x : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hqφx, mul_one]

/-- One integration by parts with a nonzero frequency. -/
theorem integral_oscillatoryPhase_mul_eq {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1)
    {t : ℝ} (ht : t ≠ 0) :
    (∫ x, oscillatoryPhase φ t x * a x) =
      -((t : ℂ) * Complex.I)⁻¹ *
        ∫ x, oscillatoryPhase φ t x * nonstationaryAmplitude q a x := by
  rw [integral_oscillatoryPhase_mul_amplitude hφ hq ha hac hqφ]
  field_simp [Complex.ofReal_ne_zero.mpr ht]

/-- Exact repeated integration by parts; no nonstationarity away from the support is used. -/
theorem integral_oscillatoryPhase_mul_eq_iterate {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1)
    {t : ℝ} (ht : t ≠ 0) (N : ℕ) :
    (∫ x, oscillatoryPhase φ t x * a x) =
      (-((t : ℂ) * Complex.I)⁻¹) ^ N *
        ∫ x, oscillatoryPhase φ t x * ((nonstationaryAmplitude q)^[N] a) x := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨hNa, hNc, hNs⟩ := nonstationaryAmplitude_iterate_properties hq ha hac N
    have hNqφ : ∀ x ∈ tsupport ((nonstationaryAmplitude q)^[N] a),
        q x * deriv φ x = 1 := fun x hx ↦ hqφ x (hNs hx)
    calc
      _ = (-((t : ℂ) * Complex.I)⁻¹) ^ N *
          ∫ x, oscillatoryPhase φ t x * ((nonstationaryAmplitude q)^[N] a) x := ih
      _ = _ := by
        rw [integral_oscillatoryPhase_mul_eq hφ hq hNa hNc hNqφ ht,
          pow_succ, Function.iterate_succ_apply', mul_assoc]

/-- The transformed amplitudes in the decay estimate have finite `L¹` norms. -/
theorem integrable_nonstationaryAmplitude_iterate {q : ℝ → ℝ} {a : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (N : ℕ) :
    Integrable ((nonstationaryAmplitude q)^[N] a) := by
  obtain ⟨hNa, hNc, _⟩ := nonstationaryAmplitude_iterate_properties hq ha hac N
  exact hNa.continuous.integrable_of_hasCompactSupport hNc

/-- Arbitrary-order nonstationary decay in terms of an explicitly iterated amplitude. -/
theorem norm_integral_oscillatoryPhase_mul_le {φ q : ℝ → ℝ} {a : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1)
    {t : ℝ} (ht : t ≠ 0) (N : ℕ) :
    ‖∫ x, oscillatoryPhase φ t x * a x‖ ≤
      |t|⁻¹ ^ N * ∫ x, ‖((nonstationaryAmplitude q)^[N] a) x‖ := by
  rw [integral_oscillatoryPhase_mul_eq_iterate hφ hq ha hac hqφ ht N,
    norm_mul, norm_pow, norm_neg, norm_inv, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∫ x, ‖oscillatoryPhase φ t x * ((nonstationaryAmplitude q)^[N] a) x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, norm_oscillatoryPhase, one_mul]

end FalconerThetaGauge
