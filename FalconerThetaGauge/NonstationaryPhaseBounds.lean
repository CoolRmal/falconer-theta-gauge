/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The real-to-complex derivative identity is adapted from falconer-packing;
the factorial transport bound is new. See docs/ATTRIBUTION.md.
-/
module

public import FalconerThetaGauge.NonstationaryPhase
public import FalconerThetaGauge.RegularFunctions
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Factorial bounds for repeated nonstationary transport

The exact derivative orders are retained in each Leibniz term. This gives a
polynomial base raised to the transport order, as required by the shrinking
parameter proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem iteratedDeriv_ofReal {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (k : ℕ) :
    iteratedDeriv k (fun x ↦ (q x : ℂ)) = fun x ↦ ((iteratedDeriv k q x : ℝ) : ℂ) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [iteratedDeriv_succ]
    exact ((hq.differentiable_iteratedDeriv k
      (by exact_mod_cast ENat.natCast_lt_top k) x).hasDerivAt.ofReal_comp).deriv

theorem tsupport_iteratedDeriv_subset (k : ℕ) (f : ℝ → ℂ) :
    tsupport (iteratedDeriv k f) ⊆ tsupport f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- Each exact Leibniz coefficient fits the factorial of the total derivative order. -/
theorem choose_mul_factorials_le {n k i : ℕ} (hi : i ≤ k + 1) :
    (k + 1).choose i * i.factorial * (n + k + 1 - i).factorial ≤
      (n + k + 1).factorial := by
  calc
    _ ≤ (n + k + 1).choose i * i.factorial * (n + k + 1 - i).factorial :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_choose i (by omega)))
    _ = _ := Nat.choose_mul_factorial_mul_factorial (by omega)

/-- Derivatives of the actual transported amplitudes have a polynomial order cost.
Only derivatives on the original amplitude's closed support are used. -/
theorem norm_iteratedDeriv_nonstationaryAmplitude_factorial_le
    {q : ℝ → ℝ} {a : ℝ → ℂ} (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    {B A D : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (N : ℕ)
    (hqB : ∀ j ≤ N, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j q x‖ ≤ B * D ^ j * j.factorial)
    (haA : ∀ j ≤ N, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j a x‖ ≤ A * D ^ j * j.factorial)
    (n k : ℕ) (hnk : n + k ≤ N) (x : ℝ) :
    ‖iteratedDeriv k ((nonstationaryAmplitude q)^[n] a) x‖ ≤
      (B * D * (N + 1)) ^ n * A * D ^ k * (n + k).factorial := by
  by_cases hx : x ∈ tsupport a
  · induction n generalizing k with
    | zero => simpa using haA k (by simpa using hnk) x hx
    | succ n ih =>
      have hk : k + 1 ≤ N := by omega
      let C := (B * D * (N + 1)) ^ n * A * B * D ^ (k + 1)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hNa := (nonstationaryAmplitude_iterate_smooth_support hq ha n).1
      have hqr : ContDiff ℝ (k + 1 : ℕ) (fun y ↦ (q y : ℂ)) :=
        (Complex.ofRealCLM.contDiff.comp hq).of_le (by exact_mod_cast le_top)
      have har : ContDiff ℝ (k + 1 : ℕ) ((nonstationaryAmplitude q)^[n] a) :=
        hNa.of_le (by exact_mod_cast le_top)
      rw [Function.iterate_succ_apply', nonstationaryAmplitude, ← iteratedDeriv_succ']
      change ‖iteratedDeriv (k + 1)
        ((fun y ↦ (q y : ℂ)) * ((nonstationaryAmplitude q)^[n] a)) x‖ ≤ _
      rw [iteratedDeriv_mul hqr.contDiffAt har.contDiffAt]
      calc
        _ ≤ ∑ i ∈ range (k + 2),
            ‖((k + 1).choose i : ℂ) * iteratedDeriv i (fun y ↦ (q y : ℂ)) x *
              iteratedDeriv (k + 1 - i) ((nonstationaryAmplitude q)^[n] a) x‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _i ∈ range (k + 2), C * (n + k + 1).factorial := by
          apply sum_le_sum
          intro i hi
          have hik : i ≤ k + 1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
          rw [norm_mul, norm_mul, Complex.norm_natCast, iteratedDeriv_ofReal hq,
            Complex.norm_real]
          have hterm : ((k + 1).choose i : ℝ) *
              ‖iteratedDeriv i q x‖ *
              ‖iteratedDeriv (k + 1 - i) ((nonstationaryAmplitude q)^[n] a) x‖ ≤
                C * (((k + 1).choose i : ℝ) * i.factorial *
                  (n + k + 1 - i).factorial) := by
            calc
              _ ≤ ((k + 1).choose i : ℝ) * (B * D ^ i * i.factorial) *
                  ((B * D * (N + 1)) ^ n * A * D ^ (k + 1 - i) *
                    (n + (k + 1 - i)).factorial) := by
                exact mul_le_mul
                  (mul_le_mul_of_nonneg_left (hqB i (hik.trans hk) x hx)
                    (Nat.cast_nonneg _))
                  (ih _ (by omega)) (norm_nonneg _) (by positivity)
              _ = _ := by
                have heq : n + (k + 1 - i) = n + k + 1 - i := by omega
                rw [heq]
                have hp : D ^ i * D ^ (k + 1 - i) = D ^ (k + 1) := by
                  rw [← pow_add, Nat.add_sub_of_le hik]
                dsimp [C]
                linear_combination
                  ((k + 1).choose i : ℝ) * i.factorial *
                    (n + k + 1 - i).factorial * (B * D * (N + 1)) ^ n * A * B * hp
          have hcoeff : ((k + 1).choose i : ℝ) * i.factorial *
              (n + k + 1 - i).factorial ≤ (n + k + 1).factorial := by
            exact_mod_cast choose_mul_factorials_le (n := n) hik
          exact hterm.trans (mul_le_mul_of_nonneg_left hcoeff hC)
        _ = (k + 2) * C * (n + k + 1).factorial := by simp; ring
        _ ≤ (N + 1) * C * (n + k + 1).factorial := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_right _ hC
          exact_mod_cast (show k + 2 ≤ N + 1 by omega)
        _ = _ := by
          rw [show n + 1 + k = n + k + 1 by omega, pow_succ]
          dsimp [C]
          rw [pow_succ]
          ring
  · have hsupport := (tsupport_iteratedDeriv_subset k _).trans
      (nonstationaryAmplitude_iterate_smooth_support hq ha n).2
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupport h)), norm_zero]
    positivity

/-- The ordinary integral of a bounded transported amplitude is controlled by
the actual original support length. -/
theorem integral_norm_le_tsupport_mass {a b : ℝ → ℂ} (hac : HasCompactSupport a)
    (hb : Integrable b) (hs : tsupport b ⊆ tsupport a) {C : ℝ}
    (hC : ∀ x, ‖b x‖ ≤ C) : (∫ x, ‖b x‖) ≤ volume.real (tsupport a) * C := by
  have he : (∫ x in tsupport a, ‖b x‖) = ∫ x, ‖b x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), norm_zero]
  rw [← he]
  calc
    _ ≤ ∫ _ in tsupport a, C :=
      setIntegral_mono_on hb.norm.integrableOn
        (integrableOn_const hac.isCompact.measure_ne_top)
        (isClosed_tsupport a).measurableSet (fun x _ ↦ hC x)
    _ = _ := by simp only [integral_const, Measure.restrict_apply_univ, Measure.real,
      smul_eq_mul]

/-- The polynomial-order nonstationary bound needed at scale-dependent parameters. -/
theorem norm_integral_oscillatoryPhase_mul_factorial_le
    {φ q : ℝ → ℝ} {a : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1)
    {B A D : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D) (N : ℕ)
    (hqB : ∀ j ≤ N, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j q x‖ ≤ B * D ^ j * j.factorial)
    (haA : ∀ j ≤ N, ∀ x ∈ tsupport a,
      ‖iteratedDeriv j a x‖ ≤ A * D ^ j * j.factorial)
    {t : ℝ} (ht : t ≠ 0) :
    ‖∫ x, oscillatoryPhase φ t x * a x‖ ≤
      volume.real (tsupport a) * A * (B * D * (N + 1) ^ 2 / |t|) ^ N := by
  have hfact : (N.factorial : ℝ) ≤ (N + 1) ^ N := by
    exact_mod_cast (Nat.factorial_le_pow N).trans
      (Nat.pow_le_pow_left (Nat.le_succ N) N)
  have hbound : ∀ x, ‖((nonstationaryAmplitude q)^[N] a) x‖ ≤
      A * (B * D * (N + 1) ^ 2) ^ N := by
    intro x
    have h := norm_iteratedDeriv_nonstationaryAmplitude_factorial_le hq ha
      hB hA hD N hqB haA N 0 (by omega) x
    simp only [iteratedDeriv_zero, pow_zero, mul_one, Nat.add_zero] at h
    calc
      _ ≤ (B * D * (N + 1)) ^ N * A * N.factorial := h
      _ ≤ (B * D * (N + 1)) ^ N * A * (N + 1) ^ N :=
        mul_le_mul_of_nonneg_left hfact (by positivity)
      _ = _ := by simp only [pow_two, mul_pow]; ring
  have hsupport := (nonstationaryAmplitude_iterate_properties hq ha hac N).2.2
  calc
    _ ≤ |t|⁻¹ ^ N * ∫ x, ‖((nonstationaryAmplitude q)^[N] a) x‖ :=
      norm_integral_oscillatoryPhase_mul_le hφ hq ha hac hqφ ht N
    _ ≤ |t|⁻¹ ^ N * (volume.real (tsupport a) *
        (A * (B * D * (N + 1) ^ 2) ^ N)) :=
      mul_le_mul_of_nonneg_left (integral_norm_le_tsupport_mass hac
        (integrable_nonstationaryAmplitude_iterate hq ha hac N) hsupport hbound)
        (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_pow]; ring

end FalconerThetaGauge
