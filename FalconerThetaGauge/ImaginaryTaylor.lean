module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The sharp Taylor remainder for a purely imaginary exponential

The integral remainder uses the constant unit norm of every derivative.
Integrating its polynomial weight gives the exact factorial denominator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ContDiff

namespace FalconerThetaGauge

def imaginaryExponential (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

theorem contDiff_imaginaryExponential : ContDiff ℝ ∞ imaginaryExponential :=
  (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

theorem hasDerivAt_imaginaryExponential (x : ℝ) :
    HasDerivAt imaginaryExponential (imaginaryExponential x * Complex.I) x := by
  change HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I))
    (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x
  simpa only [id_eq, Complex.ofReal_one, one_mul] using
    ((hasDerivAt_id x).ofReal_comp.mul_const Complex.I).cexp

theorem iteratedDeriv_imaginaryExponential (n : ℕ) (x : ℝ) :
    iteratedDeriv n imaginaryExponential x = Complex.I ^ n * imaginaryExponential x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n imaginaryExponential =
      fun t ↦ Complex.I ^ n * imaginaryExponential t from funext ih]
    rw [deriv_const_mul_field, (hasDerivAt_imaginaryExponential x).deriv, pow_succ]
    ring

theorem norm_imaginaryExponential (x : ℝ) : ‖imaginaryExponential x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem integral_one_sub_pow (n : ℕ) :
    (∫ t : ℝ in 0..1, (1 - t) ^ n) = 1 / (n + 1 : ℝ) := by
  have h := intervalIntegral.integral_comp_sub_mul (fun t : ℝ ↦ t ^ n)
    (a := 0) (b := 1) (by norm_num : (1 : ℝ) ≠ 0) 1
  simpa using h

/-- The precise integral remainder at every real argument. -/
theorem imaginaryExponential_taylor_remainder (y : ℝ) (n : ℕ) :
    imaginaryExponential y =
      (∑ k ∈ range (n + 1), ((k.factorial : ℝ)⁻¹ * y ^ k) • Complex.I ^ k) +
      (n.factorial : ℝ)⁻¹ • ∫ t : ℝ in 0..1,
        (1 - t) ^ n • (y ^ (n + 1) •
          (Complex.I ^ (n + 1) * imaginaryExponential (t * y))) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := imaginaryExponential) (x := 0) (y := y) (n := n)
    (fun _ _ ↦ contDiff_imaginaryExponential.contDiffAt.of_le (by simp))
  simpa only [zero_add, smul_eq_mul, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    prod_const, card_univ, Fintype.card_fin, iteratedDeriv_imaginaryExponential,
    imaginaryExponential, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one, smul_smul] using h

/-- The exact factorial remainder bound needed in quadratic stationary phase. -/
theorem norm_imaginaryExponential_sub_sum_le (y : ℝ) (T : ℕ) :
    ‖imaginaryExponential y -
      ∑ k ∈ range T, ((k.factorial : ℝ)⁻¹ * y ^ k) • Complex.I ^ k‖ ≤
      |y| ^ T / T.factorial := by
  cases T with
  | zero => simp [norm_imaginaryExponential]
  | succ n =>
    rw [imaginaryExponential_taylor_remainder y n, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    have hbound : ‖∫ t : ℝ in 0..1,
        (1 - t) ^ n • (y ^ (n + 1) •
          (Complex.I ^ (n + 1) * imaginaryExponential (t * y)))‖ ≤
        |y| ^ (n + 1) / (n + 1) := by
      calc
        _ ≤ ∫ t : ℝ in 0..1, (1 - t) ^ n * |y| ^ (n + 1) := by
          apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
          · exact Filter.Eventually.of_forall fun t ht ↦ by
              simp only [norm_smul, Real.norm_eq_abs, norm_mul,
                norm_pow, Complex.norm_I, norm_imaginaryExponential, one_pow,
                mul_one, abs_of_nonneg (sub_nonneg.mpr ht.2)]
              exact le_rfl
          · exact (by fun_prop : Continuous (fun t : ℝ ↦
              (1 - t) ^ n * |y| ^ (n + 1))).intervalIntegrable _ _
        _ = _ := by rw [intervalIntegral.integral_mul_const, integral_one_sub_pow]; ring
    have h := mul_le_mul_of_nonneg_left hbound
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n.factorial))
    convert h using 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

end FalconerThetaGauge
