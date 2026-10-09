/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierSeparationDerivativeExpansion
public import FalconerThetaGauge.PolynomialWeightedNorm

/-! # Actual Leibniz branch coefficient budgets for inverse operators -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset Polynomial
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem sum_abs_scheduledSymbolPair_derivative_coefficients_le
    (d₁ d₂ : ScheduledSymbolData) {T : ℕ} (E : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (l : ℕ) (horder₁ : d₁.order I₁ + l ≤ 8 * T)
    (horder₂ : d₂.order I₂ + l ≤ 8 * T) :
    (∑ s ∈ range (l + 1), ∑ b₁ : ScheduledSymbolBranch I₁ s,
      ∑ b₂ : ScheduledSymbolBranch I₂ (l - s),
        |(l.choose s : ℝ) * d₁.branchCoefficient E I₁ s b₁ *
          d₂.branchCoefficient E I₂ (l - s) b₂|) ≤
      (scheduledSymbolScale T E I₁ L₁ + scheduledSymbolScale T E I₂ L₂) ^ l := by
  calc
    _ = ∑ s ∈ range (l + 1), (l.choose s : ℝ) *
        (∑ b₁ : ScheduledSymbolBranch I₁ s, |d₁.branchCoefficient E I₁ s b₁|) *
        (∑ b₂ : ScheduledSymbolBranch I₂ (l - s),
          |d₂.branchCoefficient E I₂ (l - s) b₂|) := by
      apply sum_congr rfl
      intro s _
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (l.choose s) :
        (0 : ℝ) ≤ l.choose s)]
      simp_rw [← mul_sum]
      rw [← sum_mul, ← mul_sum]
    _ ≤ ∑ s ∈ range (l + 1), (l.choose s : ℝ) *
        scheduledSymbolScale T E I₁ L₁ ^ s * scheduledSymbolScale T E I₂ L₂ ^ (l - s) := by
      apply sum_le_sum
      intro s hs
      have hsl : s ≤ l := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hs
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (d₁.sum_abs_branchCoefficients_le E I₁ hL₁ s (by omega)) (Nat.cast_nonneg _))
        (d₂.sum_abs_branchCoefficients_le E I₂ hL₂ (l - s) (by omega))
        (sum_nonneg (fun _ _ ↦ abs_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (scheduledSymbolScale_nonneg _ _ _ _) _))
    _ = _ := by
      rw [add_pow]
      apply sum_congr rfl
      intro s _
      ring

theorem polynomialDifferentialAction_scheduledSymbolPair_eq (p : Polynomial ℂ)
    (d₁ d₂ : ScheduledSymbolData) (ρ₁ ρ₂ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I₁ I₂ : Finset ProfileScheduleTest) (x y : Plane) (θ : ℝ) :
    polynomialDifferentialAction p
      (fun t ↦ (d₁.symbol ρ₁ E width K I₁ x (unitCircleOfAngle t) : ℂ) *
        (d₂.symbol ρ₂ E width K I₂ y (unitCircleOfAngle t) : ℂ)) θ =
      ∑ l ∈ p.support, ∑ s ∈ range (l + 1), ∑ b₁ : ScheduledSymbolBranch I₁ s,
        ∑ b₂ : ScheduledSymbolBranch I₂ (l - s),
          (p.coeff l * (l.choose s : ℂ) * (d₁.branchCoefficient E I₁ s b₁ : ℂ) *
            (d₂.branchCoefficient E I₂ (l - s) b₂ : ℂ)) *
          ((d₁.branchData I₁ s b₁).symbol ρ₁ E width K I₁ x
            (unitCircleOfAngle θ) : ℂ) *
          ((d₂.branchData I₂ (l - s) b₂).symbol ρ₂ E width K I₂ y
            (unitCircleOfAngle θ) : ℂ) := by
  simp only [polynomialDifferentialAction, Polynomial.sum_def]
  simp_rw [scheduledSymbolPair_iteratedDeriv_eq, mul_sum]
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro b₁ _
  apply sum_congr rfl
  intro b₂ _
  ring

theorem sum_norm_scheduledSymbolPair_operator_coefficients_le (p : Polynomial ℂ)
    (d₁ d₂ : ScheduledSymbolData) {T : ℕ} (E : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (horder₁ : d₁.order I₁ + p.natDegree ≤ 8 * T)
    (horder₂ : d₂.order I₂ + p.natDegree ≤ 8 * T) :
    (∑ l ∈ p.support, ∑ s ∈ range (l + 1), ∑ b₁ : ScheduledSymbolBranch I₁ s,
      ∑ b₂ : ScheduledSymbolBranch I₂ (l - s),
        ‖p.coeff l * (l.choose s : ℂ) * (d₁.branchCoefficient E I₁ s b₁ : ℂ) *
          (d₂.branchCoefficient E I₂ (l - s) b₂ : ℂ)‖) ≤
      polynomialWeightedNorm p
        (scheduledSymbolScale T E I₁ L₁ + scheduledSymbolScale T E I₂ L₂) := by
  calc
    _ = ∑ l ∈ p.support, ‖p.coeff l‖ *
        (∑ s ∈ range (l + 1), ∑ b₁ : ScheduledSymbolBranch I₁ s,
          ∑ b₂ : ScheduledSymbolBranch I₂ (l - s),
            |(l.choose s : ℝ) * d₁.branchCoefficient E I₁ s b₁ *
              d₂.branchCoefficient E I₂ (l - s) b₂|) := by
      apply sum_congr rfl
      intro l _
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro b₁ _
      apply sum_congr rfl
      intro b₂ _
      simp only [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg (l.choose s) : (0 : ℝ) ≤ l.choose s)]
      ring
    _ ≤ ∑ l ∈ p.support, ‖p.coeff l‖ *
        (scheduledSymbolScale T E I₁ L₁ + scheduledSymbolScale T E I₂ L₂) ^ l := by
      apply sum_le_sum
      intro l hl
      have hlp := le_natDegree_of_ne_zero (mem_support_iff.mp hl)
      exact mul_le_mul_of_nonneg_left
        (sum_abs_scheduledSymbolPair_derivative_coefficients_le d₁ d₂ E I₁ I₂ hL₁ hL₂ l
          (by omega) (by omega)) (norm_nonneg _)
    _ = _ := rfl

end FalconerThetaGauge
