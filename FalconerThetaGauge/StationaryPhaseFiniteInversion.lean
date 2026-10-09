module

public import FalconerThetaGauge.StationaryPhaseTruncatedConvolution
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Exact finite-series inversion of the literal stationary-phase differential operators -/

@[expose] public section

noncomputable section

open Finset Polynomial
open scoped ContDiff

namespace FalconerThetaGauge

theorem sum_lower_triangle_eq_sum_orders {α : Type*} [AddCommMonoid α]
    (T : ℕ) (f : ℕ → ℕ → α) :
    (∑ p ∈ ((range T).product (range T)).filter (fun p ↦ p.1 + p.2 < T), f p.1 p.2) =
      ∑ m ∈ range T, ∑ i ∈ range (m + 1), f i (m - i) := by
  classical
  calc
    _ = ∑ p ∈ (range T).sigma (fun m ↦ antidiagonal m), f p.2.1 p.2.2 := by
      apply sum_bij (fun p _ ↦ (⟨p.1 + p.2, p⟩ : Σ _ : ℕ, ℕ × ℕ))
      · intro p hp
        simp only [mem_filter] at hp
        simp only [mem_sigma, mem_range, mem_antidiagonal]
        exact ⟨hp.2, trivial⟩
      · intro p hp q hq he
        exact congrArg (fun s : Σ _ : ℕ, ℕ × ℕ ↦ s.2) he
      · rintro ⟨m, i, j⟩ hp
        simp only [mem_sigma, mem_range, mem_antidiagonal] at hp
        have hmem : (i, j) ∈ ((range T).product (range T)).filter
            (fun p ↦ p.1 + p.2 < T) := by
          apply mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, ?_⟩
          all_goals omega
        refine ⟨(i, j), hmem, ?_⟩
        simp only [hp.2]
      · intro p hp; rfl
    _ = _ := by
      rw [sum_sigma]
      apply sum_congr rfl
      intro m hm
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ f m

theorem sum_rectangle_eq_sum_orders {α : Type*} [AddCommMonoid α]
    (T : ℕ) (f : ℕ → ℕ → α) :
    (∑ p ∈ (range T).product (range T), f p.1 p.2) =
      ∑ m ∈ range (2 * T), ∑ i ∈ range (m + 1),
        if i < T ∧ m - i < T then f i (m - i) else 0 := by
  classical
  calc
    _ = ∑ p ∈ (range (2 * T)).sigma
        (fun m ↦ (antidiagonal m).filter (fun p ↦ p.1 < T ∧ p.2 < T)),
        f p.2.1 p.2.2 := by
      apply sum_bij (fun p _ ↦ (⟨p.1 + p.2, p⟩ : Σ _ : ℕ, ℕ × ℕ))
      · intro p hp
        have hp' := Finset.mem_product.mp hp
        have h1 := mem_range.mp hp'.1
        have h2 := mem_range.mp hp'.2
        simp only [mem_sigma, mem_range, mem_filter, mem_antidiagonal]
        exact ⟨by omega, trivial, h1, h2⟩
      · intro p hp q hq he
        exact congrArg (fun s : Σ _ : ℕ, ℕ × ℕ ↦ s.2) he
      · rintro ⟨m, i, j⟩ hp
        simp only [mem_sigma, mem_range, mem_filter, mem_antidiagonal] at hp
        have hmem : (i, j) ∈ (range T).product (range T) :=
          Finset.mem_product.mpr ⟨mem_range.mpr hp.2.2.1, mem_range.mpr hp.2.2.2⟩
        refine ⟨(i, j), hmem, ?_⟩
        simp only [hp.2.1]
      · intro p hp; rfl
    _ = _ := by
      rw [sum_sigma]
      apply sum_congr rfl
      intro m hm
      rw [sum_filter]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ if i < T ∧ j < T then f i j else 0) m

/-- The literal finite double series before stationary-phase cancellation. -/
def stationaryPhaseFiniteProduct (T : ℕ) (z : ℂ) (G : ℝ → ℂ) (φ : ℝ) : ℂ :=
  ∑ p ∈ (range T).product (range T), z ^ p.1 * z ^ p.2 *
    stationaryPhaseOperator p.1 (stationaryPhaseInverseOperator p.2 G) φ

/-- These are exactly the terms of total order at least `T` in the finite product. -/
def stationaryPhaseFiniteTail (T : ℕ) (z : ℂ) (G : ℝ → ℂ) (φ : ℝ) : ℂ :=
  ∑ p ∈ ((range T).product (range T)).filter (fun p ↦ T ≤ p.1 + p.2),
    z ^ p.1 * z ^ p.2 *
      stationaryPhaseOperator p.1 (stationaryPhaseInverseOperator p.2 G) φ

theorem stationaryPhaseFiniteProduct_eq_sum {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (T : ℕ) (z : ℂ) (φ : ℝ) :
    stationaryPhaseFiniteProduct T z G φ =
      ∑ m ∈ range (2 * T), z ^ m *
        polynomialDifferentialAction (stationaryPhaseTruncatedConvolution T m) G φ := by
  rw [stationaryPhaseFiniteProduct, sum_rectangle_eq_sum_orders T (fun i j ↦
    z ^ i * z ^ j * stationaryPhaseOperator i (stationaryPhaseInverseOperator j G) φ)]
  apply sum_congr rfl
  intro m hm
  rw [stationaryPhaseTruncatedConvolution, polynomialDifferentialAction_sum]
  simp only [Finset.sum_apply, mul_sum]
  apply sum_congr rfl
  intro i hi
  split_ifs with hpass
  · rw [polynomialDifferentialAction_mul hG, stationaryPhasePolynomial_action]
    rw [← pow_add, Nat.add_sub_of_le (by have := mem_range.mp hi; omega)]
    rfl
  · simp only [polynomialDifferentialAction_zero, Pi.zero_apply, mul_zero]

/-- No low-order remainder is assumed: the actual recursion cancels it identically. -/
theorem stationaryPhaseFiniteProduct_eq_add_tail {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    {T : ℕ} (hT : 0 < T) (z : ℂ) (φ : ℝ) :
    stationaryPhaseFiniteProduct T z G φ = G φ + stationaryPhaseFiniteTail T z G φ := by
  have hsplit := sum_filter_add_sum_filter_not ((range T).product (range T))
    (fun p ↦ p.1 + p.2 < T) (fun p ↦ z ^ p.1 * z ^ p.2 *
      stationaryPhaseOperator p.1 (stationaryPhaseInverseOperator p.2 G) φ)
  have hlo : (∑ p ∈ ((range T).product (range T)).filter (fun p ↦ p.1 + p.2 < T),
      z ^ p.1 * z ^ p.2 *
        stationaryPhaseOperator p.1 (stationaryPhaseInverseOperator p.2 G) φ) = G φ := by
    rw [sum_lower_triangle_eq_sum_orders T (fun i j ↦
      z ^ i * z ^ j * stationaryPhaseOperator i (stationaryPhaseInverseOperator j G) φ)]
    simp_rw [stationaryPhase_scaled_inverse_cancellation hG]
    exact sum_eq_single_of_mem 0 (mem_range.mpr hT) (by intro b hb hne; simp [hne])
  simpa only [hlo, stationaryPhaseFiniteProduct, stationaryPhaseFiniteTail, not_lt] using
    hsplit.symm

theorem stationaryPhaseFiniteTail_eq_sum {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    {T : ℕ} (hT : 0 < T) (z : ℂ) (φ : ℝ) :
    stationaryPhaseFiniteTail T z G φ =
      ∑ k ∈ range T, z ^ (T + k) *
        polynomialDifferentialAction (stationaryPhaseTruncatedConvolution T (T + k)) G φ := by
  have hlo : (∑ m ∈ range T, z ^ m *
      polynomialDifferentialAction (stationaryPhaseTruncatedConvolution T m) G φ) = G φ := by
    rw [sum_eq_single_of_mem 0 (mem_range.mpr hT) (by
      intro m hm hne
      rw [stationaryPhaseTruncatedConvolution_below (mem_range.mp hm), ite_eq_right hne,
        polynomialDifferentialAction_zero]
      simp)]
    rw [stationaryPhaseTruncatedConvolution_below hT]
    simp [polynomialDifferentialAction_one]
  have hp := stationaryPhaseFiniteProduct_eq_sum hG T z φ
  rw [show 2 * T = T + T by omega, sum_range_add, hlo] at hp
  rw [stationaryPhaseFiniteProduct_eq_add_tail hG hT] at hp
  exact add_left_cancel hp

/-- Each actual omitted coefficient has the literal source inversion-tail norm. -/
theorem norm_stationaryPhaseFiniteTail_le {G : ℝ → ℂ} (hGs : ContDiff ℝ ∞ G)
    {T : ℕ} (hT : 0 < T) {A M : ℝ} (hG : IsDerivativeRegular A M (4 * T) G)
    (z : ℂ) (φ : ℝ) :
    ‖stationaryPhaseFiniteTail T z G φ‖ ≤
      ∑ k ∈ range T, A * (T + k + 1) * (800 * (T + k) * M ^ 2 * ‖z‖) ^ (T + k) := by
  rw [stationaryPhaseFiniteTail_eq_sum hGs hT]
  calc
    _ ≤ ∑ k ∈ range T, ‖z ^ (T + k) *
        polynomialDifferentialAction (stationaryPhaseTruncatedConvolution T (T + k)) G φ‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro k hk
      have hkT : k < T := mem_range.mp hk
      rw [norm_mul, norm_pow]
      calc
        _ ≤ ‖z‖ ^ (T + k) *
            (A * (T + k + 1) * (800 * (T + k) * M ^ 2) ^ (T + k)) :=
          mul_le_mul_of_nonneg_left
            (by
              have hb := norm_stationaryPhaseTruncatedConvolution_action_le T (T + k)
                (hG.of_le (by omega)) φ
              simpa only [Nat.cast_add] using hb) (by positivity)
        _ = _ := by
          conv_rhs => rw [mul_pow]
          ring

end FalconerThetaGauge
