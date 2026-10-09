/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsPiecesDerivatives

/-! # Derivative budgets from the actual longest scheduled test -/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped Classical

namespace FalconerThetaGauge

theorem inv_scheduledMaskScale (E : ℝ) (test : ProfileScheduleTest) :
    (scheduledMaskScale E test)⁻¹ = max 1 ((2 : ℝ) ^ ((test.length : ℝ) - E)) := by
  have ha : 0 < (2 : ℝ) ^ (E - (test.length : ℝ)) := by positivity
  have hscale : scheduledMaskScale E test = min 1 ((2 : ℝ) ^ (E - (test.length : ℝ))) := by
    unfold scheduledMaskScale
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  have hi : ((2 : ℝ) ^ (E - (test.length : ℝ)))⁻¹ =
      (2 : ℝ) ^ ((test.length : ℝ) - E) := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hscale, ← hi]
  by_cases h : 1 ≤ (2 : ℝ) ^ (E - (test.length : ℝ))
  · rw [min_eq_left h, inv_one, max_eq_left ((inv_le_one₀ ha).mpr h)]
  · have hle := le_of_not_ge h
    rw [min_eq_right hle, max_eq_right ((one_le_inv₀ ha).mpr hle)]

theorem scheduledTestDerivativeScale_le_length {T L : ℕ} {E : ℝ}
    {test : ProfileScheduleTest} (hL : test.length ≤ L) :
    scheduledTestDerivativeScale T E test ≤
      (4 * (T : ℝ)) ^ 3 * max 1 ((2 : ℝ) ^ ((L : ℝ) - E)) := by
  rw [scheduledTestDerivativeScale, div_eq_mul_inv, inv_scheduledMaskScale]
  apply mul_le_mul_of_nonneg_left
  · apply max_le_max_left
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact sub_le_sub_right (by exact_mod_cast hL) E
  · positivity

/-- The finite product scale is paid by the test count and their actual maximum length. -/
theorem sum_scheduledTestDerivativeScale_le (I : Finset ProfileScheduleTest) (T : ℕ) (E : ℝ)
    {L : ℕ} (hL : ∀ test ∈ I, test.length ≤ L) :
    (∑ test ∈ I, scheduledTestDerivativeScale T E test) ≤
      (I.card : ℝ) * (4 * (T : ℝ)) ^ 3 * max 1 ((2 : ℝ) ^ ((L : ℝ) - E)) := by
  calc
    _ ≤ ∑ _test ∈ I, ((4 * (T : ℝ)) ^ 3 * max 1 ((2 : ℝ) ^ ((L : ℝ) - E))) :=
      Finset.sum_le_sum (fun test ht => scheduledTestDerivativeScale_le_length (hL test ht))
    _ = _ := by simp [mul_assoc]

theorem sum_scheduledTestDerivativeScale_le_sup (I : Finset ProfileScheduleTest)
    (T : ℕ) (E : ℝ) :
    (∑ test ∈ I, scheduledTestDerivativeScale T E test) ≤
      (I.card : ℝ) * (4 * (T : ℝ)) ^ 3 *
        max 1 ((2 : ℝ) ^ (((I.sup ProfileScheduleTest.length : ℕ) : ℝ) - E)) :=
  sum_scheduledTestDerivativeScale_le I T E (fun _ ht => Finset.le_sup ht)

/-- The manuscript's common per-pin list bound supplies the literal polynomial prefactor. -/
theorem sum_scheduledTestDerivativeScale_le_scale_sq (I : Finset ProfileScheduleTest)
    {N : ℕ} (hcard : I.card ≤ N ^ 2 + 1) (T : ℕ) (E : ℝ)
    {L : ℕ} (hL : ∀ test ∈ I, test.length ≤ L) :
    (∑ test ∈ I, scheduledTestDerivativeScale T E test) ≤
      ((N : ℝ) ^ 2 + 1) * (4 * (T : ℝ)) ^ 3 * max 1 ((2 : ℝ) ^ ((L : ℝ) - E)) := by
  apply (sum_scheduledTestDerivativeScale_le I T E hL).trans
  have hcard' : (I.card : ℝ) ≤ (N : ℝ) ^ 2 + 1 := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard' (by positivity))
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _))

theorem IsDerivativeRegular.mono_scale {A M P : ℝ} {k : ℕ} {f : ℝ → ℂ}
    (hf : IsDerivativeRegular A M k f) (hMP : M ≤ P) : IsDerivativeRegular A P k f := by
  refine ⟨hf.amplitude_nonneg, hf.one_le_scale.trans hMP, hf.smooth, ?_⟩
  intro j hj x
  apply (hf.bound j hj x).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hf.one_le_scale]) hMP j)
    hf.amplitude_nonneg

/-- The actual assembled mask obeys the explicit per-pin count and maximum-length budget. -/
theorem regularDirectionalFilter_symbol_derivative_budget (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    {T : ℕ} (hT : 2 ≤ T)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    {x : Plane} (hx : x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val)
    {L : ℕ} (hL : ∀ test ∈ regularMeasurePieceTests
      (regularDyadicPartMeasure μ (tolerance θ N) N t.val) θ N, test.length ≤ L) :
    IsDerivativeRegular 1
      (((N : ℝ) ^ 2 + 1) * (4 * (T : ℝ)) ^ 3 *
        max 1 ((2 : ℝ) ^ ((L : ℝ) - tolerance θ N * N))) (6 * T)
      (fun α => ((regularDirectionalFilter μ hpar (6 * T)).symbol x
        (unitCircleOfAngle α) : ℂ)) := by
  apply (regularDirectionalFilter_symbol_isDerivativeRegular_on_piece μ hpar hT t hx).mono_scale
  apply sum_scheduledTestDerivativeScale_le_scale_sq _ _ T (tolerance θ N * N) hL
  exact profilePieceTests_card_le_scale_sq_add_one _ hpar

/-- Choosing the true maximum gives a fully concrete bound without a length hypothesis. -/
theorem regularDirectionalFilter_symbol_derivative_budget_sup (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    {T : ℕ} (hT : 2 ≤ T)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    {x : Plane} (hx : x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val) :
    let I := regularMeasurePieceTests (regularDyadicPartMeasure μ (tolerance θ N) N t.val) θ N
    IsDerivativeRegular 1
      (((N : ℝ) ^ 2 + 1) * (4 * (T : ℝ)) ^ 3 *
        max 1 ((2 : ℝ) ^ (((I.sup ProfileScheduleTest.length : ℕ) : ℝ) - tolerance θ N * N)))
      (6 * T)
      (fun α => ((regularDirectionalFilter μ hpar (6 * T)).symbol x (unitCircleOfAngle α) : ℂ)) :=
  regularDirectionalFilter_symbol_derivative_budget μ hpar hT t hx (fun _ ht => Finset.le_sup ht)

end FalconerThetaGauge
