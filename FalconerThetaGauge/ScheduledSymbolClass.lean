module

public import FalconerThetaGauge.ScheduledSymbolFactors

/-! # The manuscript's actual class of symbols built from a finite scheduled test list -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

/-- Only the literal spatial weight and derivative choices are data; no energy bound is assumed. -/
structure ScheduledSymbolData where
  spatialWeight : Plane → ℝ
  derivativeOrders : ProfileScheduleTest → ℕ
  measurable_spatialWeight : Measurable spatialWeight
  abs_spatialWeight_le_one : ∀ x, |spatialWeight x| ≤ 1

def ScheduledSymbolData.order (d : ScheduledSymbolData) (I : Finset ProfileScheduleTest) : ℕ :=
  ∑ test ∈ I, d.derivativeOrders test

def ScheduledSymbolData.symbol (d : ScheduledSymbolData) (ρ : Measure Plane) (E width : ℝ)
    (K : ℕ) (I : Finset ProfileScheduleTest) : Plane → UnitCircle → ℝ :=
  fun x w ↦ d.spatialWeight x * ∏ test ∈ I,
    normalizedScheduledTestSymbol ρ E width test K (d.derivativeOrders test) x w

/-- Definition 6.10 as a concrete set of functions with actual finite-product witnesses. -/
def scheduledSymbolClass (ρ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (k₀ : ℕ) : Set (Plane → UnitCircle → ℝ) :=
  {b | ∃ d : ScheduledSymbolData, d.order I ≤ k₀ ∧ b = d.symbol ρ E width K I}

def ScheduledSymbolData.maskProduct : ScheduledSymbolData where
  spatialWeight := fun _ ↦ 1
  derivativeOrders := fun _ ↦ 0
  measurable_spatialWeight := measurable_const
  abs_spatialWeight_le_one := by intro x; norm_num

theorem ScheduledSymbolData.maskProduct_order (I : Finset ProfileScheduleTest) :
    ScheduledSymbolData.maskProduct.order I = 0 := by
  simp [ScheduledSymbolData.order, ScheduledSymbolData.maskProduct]

theorem ScheduledSymbolData.maskProduct_symbol (ρ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) :
    ScheduledSymbolData.maskProduct.symbol ρ E width K I =
      scheduledWidthMaskProduct ρ E width K I := by
  ext x w
  simp only [ScheduledSymbolData.symbol, ScheduledSymbolData.maskProduct,
    normalizedScheduledTestSymbol_zero, one_mul, scheduledWidthMaskProduct]

theorem scheduledWidthMaskProduct_mem_symbolClass (ρ : Measure Plane) (E width : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) (k₀ : ℕ) :
    scheduledWidthMaskProduct ρ E width K I ∈ scheduledSymbolClass ρ E width K I k₀ :=
  ⟨.maskProduct, by simp [ScheduledSymbolData.maskProduct_order],
    (ScheduledSymbolData.maskProduct_symbol ρ E width K I).symm⟩

theorem ScheduledSymbolData.derivativeOrders_le_order (d : ScheduledSymbolData)
    (I : Finset ProfileScheduleTest) {test : ProfileScheduleTest} (ht : test ∈ I) :
    d.derivativeOrders test ≤ d.order I :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ht

theorem ScheduledSymbolData.measurable_symbol (d : ScheduledSymbolData) (ρ : Measure Plane)
    (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) :
    Measurable (uncurry (d.symbol ρ E width K I)) := by
  exact (d.measurable_spatialWeight.comp measurable_fst).mul
    (Finset.measurable_prod I fun test _ ↦
      measurable_normalizedScheduledTestSymbol ρ E width test K (d.derivativeOrders test))

theorem ScheduledSymbolData.contDiff_symbol_comp_angle (d : ScheduledSymbolData)
    (ρ : Measure Plane) (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (x : Plane) :
    ContDiff ℝ ∞ (fun θ ↦ d.symbol ρ E width K I x (unitCircleOfAngle θ)) :=
  contDiff_const.mul (contDiff_prod fun test _ ↦
    contDiff_normalizedScheduledTestSymbol_comp_angle ρ E width test K (d.derivativeOrders test) x)

/-- S1, proved from each actual normalized mask rather than a bound in the class definition. -/
theorem ScheduledSymbolData.abs_symbol_le_one (d : ScheduledSymbolData) (ρ : Measure Plane)
    (E width : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (horder : d.order I ≤ K)
    (x : Plane) (w : UnitCircle) : |d.symbol ρ E width K I x w| ≤ 1 := by
  rw [ScheduledSymbolData.symbol, abs_mul, Finset.abs_prod]
  calc
    _ ≤ 1 * 1 := mul_le_mul (d.abs_spatialWeight_le_one x)
      (Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun test ht ↦ by
        simpa only [Real.norm_eq_abs] using norm_normalizedScheduledTestSymbol_le_one ρ E width
          test K (d.derivativeOrders test) ((d.derivativeOrders_le_order I ht).trans horder) x w)
      (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

theorem abs_le_one_of_mem_scheduledSymbolClass (ρ : Measure Plane) (E width : ℝ)
    (K : ℕ) (I : Finset ProfileScheduleTest) {k₀ : ℕ} (hk : k₀ ≤ K)
    {b : Plane → UnitCircle → ℝ} (hb : b ∈ scheduledSymbolClass ρ E width K I k₀)
    (x : Plane) (w : UnitCircle) : |b x w| ≤ 1 := by
  obtain ⟨d, horder, rfl⟩ := hb
  exact d.abs_symbol_le_one ρ E width K I (horder.trans hk) x w

/-- S2 for every genuinely built symbol, including derivatives of the individual masks. -/
theorem ScheduledSymbolData.ne_zero_implies_next_passing (d : ScheduledSymbolData)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {L : ℕ} (hL : 0 < L)
    (hsize : (L : ℝ) ≤ (2 : ℝ) ^ E / 8) (i K : ℕ) (I : Finset ProfileScheduleTest)
    (hordered : ScheduledTestsOrdered I) {x : Plane} (hx : x ∈ scheduledAnchorCarrier ρ I)
    (w : UnitCircle) (hb : d.symbol ρ E (directionalLevelWidth L i) K I x w ≠ 0) :
    ∀ test ∈ I, (x, w) ∈ scheduledPassingPinSet ρ E (directionalLevelWidth L (i + 1)) test := by
  intro test ht
  obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.1 (mem_iInter₂.1 hx test ht)
  have hf := (Finset.prod_ne_zero_iff.1 (mul_ne_zero_iff.1 hb).2) test ht
  rw [normalizedScheduledTestSymbol_eq_on_cell ρ E _ test K _ hP hxP,
    normalizedCircleMaskDerivative] at hf
  have hderiv := (mul_ne_zero_iff.1 hf).2
  have heq : (fun t ↦ scheduledCircleMask ρ E (directionalLevelWidth L i) test K P
      (unitCircleOfAngle t)) = explicitPassingMask K (scheduledMaskScale E test)
        (angularPassingSet (scheduledPassingDirections ρ E (directionalLevelWidth L i) test P)) :=
    funext (circlePassingMask_comp_angle K _ _)
  rw [← heq] at hderiv
  apply (mem_scheduledPassingPinSet_on_cell ρ E _ test hP hxP w).2
  simpa only [unitCircleOfAngle_circleAngle] using
    scheduled_level_derivative_ne_zero_implies_passing ρ E hL hsize i test
      (hordered.1 test ht) (hordered.2 test ht) K (d.derivativeOrders test) P
      (Finset.mem_filter.1 hP).2 hderiv

end FalconerThetaGauge
