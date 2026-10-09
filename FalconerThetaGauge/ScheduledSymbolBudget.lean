module

public import FalconerThetaGauge.ScheduledSymbolRegularity

/-! # Full `8T` actual mask bounds and the manuscript's scale-dependent symbol budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_circlePassingMask_comp_angle_le_eight {T : ℕ} (hT : 3 ≤ T)
    {k : ℕ} (hk : k ≤ 8 * T) {δ : ℝ} (hδ : 0 < δ) (Z : Set UnitCircle) (θ : ℝ) :
    ‖iteratedDeriv k (fun t ↦ circlePassingMask (8 * T) δ Z (unitCircleOfAngle t)) θ‖ ≤
      ((4 * (T : ℝ)) ^ 3 / δ) ^ k := by
  have heq : (fun t ↦ circlePassingMask (8 * T) δ Z (unitCircleOfAngle t)) =
      explicitPassingMask (8 * T) δ (angularPassingSet Z) :=
    funext (circlePassingMask_comp_angle (8 * T) δ Z)
  rw [heq]
  exact norm_iteratedDeriv_explicitPassingMask_le_polynomial_base_eight hT hk hδ _ θ

theorem norm_iteratedDeriv_scheduledWidthTestSymbol_comp_angle_le_eight
    (ρ : Measure Plane) {T : ℕ} (hT : 3 ≤ T) (E width : ℝ) (test : ProfileScheduleTest)
    {k : ℕ} (hk : k ≤ 8 * T) (x : Plane) (θ : ℝ) :
    ‖iteratedDeriv k (fun t ↦ scheduledWidthTestSymbol ρ E width test (8 * T) x
      (unitCircleOfAngle t)) θ‖ ≤ ((4 * (T : ℝ)) ^ 3 / scheduledMaskScale E test) ^ k := by
  by_cases hx : ∃ P ∈ occupiedUnitCells ρ test.anchor, x ∈ GaugeFrostman.dyadicCube test.anchor P
  · obtain ⟨P, hP, hxP⟩ := hx
    simp_rw [scheduledWidthTestSymbol_eq_on_cell ρ E width test (8 * T) hP hxP]
    exact norm_iteratedDeriv_circlePassingMask_comp_angle_le_eight hT hk
      (scheduledMaskScale_pos E test) _ θ
  · have heq : (fun t ↦ scheduledWidthTestSymbol ρ E width test (8 * T) x
        (unitCircleOfAngle t)) = fun _ : ℝ ↦ 0 := by
      ext t
      exact partitionDirectionalSymbol_eq_zero_off_cells _ _ _
        (by simpa only [not_exists, not_and] using hx) _
    rw [heq]
    simp only [iteratedDeriv_fun_const_zero, norm_zero]
    have hs := scheduledMaskScale_pos E test
    positivity

theorem symbolPolynomialBudget_le_sourceBudget (T N : ℕ) (hN : 1 ≤ N)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1) :
    128 * (T : ℝ) ^ 2 * I.card ≤
      (2 : ℝ) ^ (80 : ℕ) * ((T : ℝ) + 1) ^ (12 : ℕ) *
        ((N : ℝ) + 16) ^ (12 : ℕ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : (I.card : ℝ) ≤ ((N : ℝ) + 16) ^ 2 := by
    have hc' : (I.card : ℝ) ≤ (N : ℝ) ^ 2 + 1 := by exact_mod_cast hcard
    nlinarith
  have hT : (T : ℝ) ^ 2 ≤ ((T : ℝ) + 1) ^ 12 := by
    calc
      _ ≤ ((T : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
      _ ≤ _ := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
        (by norm_num : 2 ≤ 12)
  have hNp : ((N : ℝ) + 16) ^ 2 ≤ ((N : ℝ) + 16) ^ 12 :=
    pow_le_pow_right₀ (by linarith) (by norm_num : 2 ≤ 12)
  have hconst : (128 : ℝ) ≤ 2 ^ (80 : ℕ) := by norm_num
  exact mul_le_mul
    (mul_le_mul hconst hT (sq_nonneg _) (by positivity)) (hc.trans hNp)
    (Nat.cast_nonneg _) (by positivity)

theorem scheduledSymbolScale_le_parameterBound {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) (I : Finset ProfileScheduleTest)
    (hcard : I.card ≤ N ^ 2 + 1) (L : ℕ) :
    scheduledSymbolScale (expansionCount θ N) (tolerance θ N * N) I L ≤
      (2 : ℝ) ^ (tolerance θ N * N / 8) *
        max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-(tolerance θ N * N))) := by
  unfold scheduledSymbolScale
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (symbolPolynomialBudget_le_sourceBudget (expansionCount θ N) N
    (by have := hpar.1; omega) I hcard).trans
    hpar.2.1

end FalconerThetaGauge
