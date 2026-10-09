module

public import FalconerThetaGauge.ScheduledSymbolClass

/-! # Exact one-step differentiation inside the genuine built symbol class -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

def ScheduledSymbolData.raise (d : ScheduledSymbolData) (test : ProfileScheduleTest) :
    ScheduledSymbolData where
  spatialWeight := d.spatialWeight
  derivativeOrders := update d.derivativeOrders test (d.derivativeOrders test + 1)
  measurable_spatialWeight := d.measurable_spatialWeight
  abs_spatialWeight_le_one := d.abs_spatialWeight_le_one

theorem ScheduledSymbolData.raise_order (d : ScheduledSymbolData)
    (I : Finset ProfileScheduleTest) {test : ProfileScheduleTest} (ht : test ∈ I) :
    (d.raise test).order I = d.order I + 1 := by
  unfold ScheduledSymbolData.order ScheduledSymbolData.raise
  rw [Finset.sum_update_of_mem ht]
  rw [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add I d.derivativeOrders ht
  omega

theorem ScheduledSymbolData.raise_symbol (d : ScheduledSymbolData) (ρ : Measure Plane)
    (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) {test : ProfileScheduleTest}
    (ht : test ∈ I) (x : Plane) (w : UnitCircle) :
    (d.raise test).symbol ρ E width K I x w = d.spatialWeight x *
      (normalizedScheduledTestSymbol ρ E width test K (d.derivativeOrders test + 1) x w *
        ∏ u ∈ I.erase test,
          normalizedScheduledTestSymbol ρ E width u K (d.derivativeOrders u) x w) := by
  rw [ScheduledSymbolData.symbol, ← Finset.mul_prod_erase _ _ ht]
  congr 1
  simp only [ScheduledSymbolData.raise, update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro u hu
  rw [update_of_ne (Finset.mem_erase.1 hu).1]

/-- This is an equality of actual derivatives and literal next-order symbols. -/
theorem ScheduledSymbolData.deriv_symbol (d : ScheduledSymbolData) (ρ : Measure Plane)
    (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (x : Plane) (θ : ℝ) :
    deriv (fun t ↦ d.symbol ρ E width K I x (unitCircleOfAngle t)) θ =
      ∑ test ∈ I, scheduledSymbolDerivativeCoefficient E test (d.derivativeOrders test) *
        (d.raise test).symbol ρ E width K I x (unitCircleOfAngle θ) := by
  change deriv (fun t ↦ d.spatialWeight x * ∏ test ∈ I,
    normalizedScheduledTestSymbol ρ E width test K (d.derivativeOrders test) x
      (unitCircleOfAngle t)) θ = _
  rw [deriv_const_mul_field, deriv_fun_finsetProd
    (fun test _ ↦ (contDiff_normalizedScheduledTestSymbol_comp_angle ρ E width test K
      (d.derivativeOrders test) x).differentiable (by simp) θ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro test ht
  rw [deriv_normalizedScheduledTestSymbol_comp_angle, d.raise_symbol ρ E width K I ht]
  simp only [smul_eq_mul]
  ring

/-- The exact source scale `M_L`, with the actual scheduled mask radii. -/
def scheduledSymbolScale (T : ℕ) (E : ℝ) (I : Finset ProfileScheduleTest) (L : ℕ) : ℝ :=
  128 * (T : ℝ) ^ 2 * I.card * max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E))

theorem scheduledSymbolScale_nonneg (T : ℕ) (E : ℝ) (I : Finset ProfileScheduleTest)
    (L : ℕ) : 0 ≤ scheduledSymbolScale T E I L := by
  unfold scheduledSymbolScale
  positivity

theorem scheduledMaskScale_inv_le (E : ℝ) (test : ProfileScheduleTest) {L : ℕ}
    (hL : test.length ≤ L) :
    (scheduledMaskScale E test)⁻¹ ≤ max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) := by
  unfold scheduledMaskScale
  by_cases hsmall : 1 ≤ (2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ E
  · rw [min_eq_left hsmall, inv_one]
    exact le_max_left _ _
  · rw [min_eq_right (le_of_not_ge hsmall)]
    have heq : ((2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ E)⁻¹ =
        (2 : ℝ) ^ (test.length : ℝ) * (2 : ℝ) ^ (-E) := by
      rw [mul_inv, ← Real.rpow_neg (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
    rw [heq]
    apply le_trans _ (le_max_right _ _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hL)

theorem scheduledSymbolDerivativeCoefficient_le {T k : ℕ} (hk : k + 1 ≤ 8 * T)
    (E : ℝ) (test : ProfileScheduleTest) {L : ℕ} (hL : test.length ≤ L) :
    scheduledSymbolDerivativeCoefficient E test k ≤
      128 * (T : ℝ) ^ 2 * max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) := by
  rw [scheduledSymbolDerivativeCoefficient, mul_assoc]
  calc
    _ ≤ (scheduledMaskScale E test)⁻¹ * (128 * (T : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (symbol_oneStep_coefficient_le hk)
        (inv_nonneg.mpr (scheduledMaskScale_pos E test).le)
    _ ≤ max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) * (128 * (T : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (scheduledMaskScale_inv_le E test hL) (by positivity)
    _ = _ := mul_comm _ _

theorem ScheduledSymbolData.sum_abs_derivativeCoefficients_le (d : ScheduledSymbolData)
    {T : ℕ} (E : ℝ) (I : Finset ProfileScheduleTest) {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) (horder : d.order I + 1 ≤ 8 * T) :
    ∑ test ∈ I, |scheduledSymbolDerivativeCoefficient E test (d.derivativeOrders test)| ≤
      scheduledSymbolScale T E I L := by
  calc
    _ ≤ ∑ _test ∈ I,
        128 * (T : ℝ) ^ 2 * max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) := by
      apply Finset.sum_le_sum
      intro test ht
      rw [abs_of_nonneg (scheduledSymbolDerivativeCoefficient_nonneg E test _)]
      exact scheduledSymbolDerivativeCoefficient_le
        (by have := d.derivativeOrders_le_order I ht; omega) E test (hL test ht)
    _ = scheduledSymbolScale T E I L := by
      simp only [Finset.sum_const, nsmul_eq_mul, scheduledSymbolScale]
      ring

end FalconerThetaGauge
