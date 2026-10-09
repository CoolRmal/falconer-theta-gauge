module

public import FalconerThetaGauge.ScalarEnergyBinningShift

/-!
# The decaying cross-kernel bound in Lemma 7.3(iii)

The positive integer tail is bounded by a finite telescoping calculation.
Countable bin correlations then control the actual two-measure integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace FalconerThetaGauge

/-- The literal polynomially decaying scalar kernel in Lemma 7.3(iii). -/
def scalarBinningKernel (h : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + |p.1 - p.2| / h) ^ (-2 : ℝ))

@[fun_prop]
theorem measurable_scalarBinningKernel (h : ℝ) : Measurable (scalarBinningKernel h) := by
  unfold scalarBinningKernel
  fun_prop

/-- The source's shift weight: one at zero and `|m|^(-2)` away from zero. -/
def scalarBinningShiftWeight (m : ℤ) : ℝ≥0∞ :=
  if m = 0 then 1 else ENNReal.ofReal ((m.natAbs : ℝ) ^ (-2 : ℝ))

theorem sum_inverse_square_succ_le (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) ≤ 2 - 2 / (N + 1 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (2 - 2 / (N + 1 : ℝ)) + ((N + 1 : ℝ) ^ (2 : ℕ))⁻¹ :=
        add_le_add ih le_rfl
      _ ≤ 2 - 2 / (N + 1 + 1 : ℝ) := by
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        have h₁ : (N + 1 : ℝ) ≠ 0 := by positivity
        have h₂ : (N + 1 + 1 : ℝ) ≠ 0 := by positivity
        field_simp
        nlinarith

theorem tsum_inverse_square_succ_le_two :
    (∑' n : ℕ, ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹)) ≤ 2 := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ by positivity)]
  apply (ENNReal.ofReal_le_ofReal _).trans_eq (ENNReal.ofReal_ofNat 2)
  exact (sum_inverse_square_succ_le N).trans (by
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ (N + 1 : ℝ))])

theorem scalarBinningShiftWeight_nat_succ (n : ℕ) :
    scalarBinningShiftWeight ((n + 1 : ℕ) : ℤ) =
      ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
  simp only [scalarBinningShiftWeight, Int.natCast_eq_zero, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Int.natAbs_natCast]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  push_cast
  rfl

theorem scalarBinningShiftWeight_neg_succ (n : ℕ) :
    scalarBinningShiftWeight (Int.negSucc n) =
      ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
  simp only [scalarBinningShiftWeight, Int.negSucc_ne_zero, ite_false, Int.natAbs_negSucc]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  push_cast
  rfl

/-- The shift weights sum to at most five, which is stronger than the source's ten. -/
theorem tsum_scalarBinningShiftWeight_le_five :
    (∑' m : ℤ, scalarBinningShiftWeight m) ≤ 5 := by
  rw [← Equiv.intEquivNatSumNat.symm.tsum_eq scalarBinningShiftWeight]
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  change (∑' n : ℕ, scalarBinningShiftWeight (n : ℤ)) +
    (∑' n : ℕ, scalarBinningShiftWeight (Int.negSucc n)) ≤ 5
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, scalarBinningShiftWeight, ite_true]
  change 1 + (∑' n : ℕ, scalarBinningShiftWeight ((n + 1 : ℕ) : ℤ)) +
    (∑' n : ℕ, scalarBinningShiftWeight (Int.negSucc n)) ≤ 5
  simp_rw [scalarBinningShiftWeight_nat_succ, scalarBinningShiftWeight_neg_succ]
  calc
    _ ≤ 1 + 2 + 2 := add_le_add (add_le_add le_rfl tsum_inverse_square_succ_le_two)
      tsum_inverse_square_succ_le_two
    _ = 5 := by norm_num

/-- The literal kernel is bounded by the source's corresponding bin-shift weight. -/
theorem scalarBinningKernel_le_shiftWeight {h : ℝ} (hh : 0 < h) (p : ℝ × ℝ) :
    scalarBinningKernel h p ≤
      scalarBinningShiftWeight (scalarBinIndex h p.1 - scalarBinIndex h p.2) := by
  let m := scalarBinIndex h p.1 - scalarBinIndex h p.2
  have hb : 1 ≤ 1 + |p.1 - p.2| / h :=
    le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hh.le)
  obtain ⟨hl, hu⟩ := scalarBin_difference_bounds
    (mem_scalarBin_index hh p.1) (mem_scalarBin_index hh p.2)
  have habs : |(m : ℝ)| ≤ 1 + |p.1 - p.2| / h := by
    have hdiv : (|p.1 - p.2| / h) * h = |p.1 - p.2| := div_mul_cancel₀ _ hh.ne'
    apply abs_le.2
    constructor
    ·
      have hd := neg_abs_le (p.1 - p.2)
      dsimp [m]
      nlinarith
    ·
      have hd := le_abs_self (p.1 - p.2)
      dsimp [m]
      nlinarith
  unfold scalarBinningKernel scalarBinningShiftWeight
  change ENNReal.ofReal ((1 + |p.1 - p.2| / h) ^ (-2 : ℝ)) ≤
    if m = 0 then 1 else ENNReal.ofReal ((m.natAbs : ℝ) ^ (-2 : ℝ))
  split_ifs with hm
  · calc
      _ ≤ ENNReal.ofReal ((1 : ℝ) ^ (-2 : ℝ)) := ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos zero_lt_one hb (by norm_num))
      _ = 1 := by norm_num
  · have hmpos : (0 : ℝ) < m.natAbs := by exact_mod_cast Int.natAbs_pos.2 hm
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_nonpos hmpos _ (by norm_num)
    have hc : (m.natAbs : ℝ) = |(m : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natCast_natAbs m)
    rw [hc]
    exact habs

/-- A weighted countable cover by the actual bin-shift rectangles. -/
theorem scalarBinningKernel_le_tsum_indicators {h : ℝ} (hh : 0 < h) (p : ℝ × ℝ) :
    scalarBinningKernel h p ≤ ∑' m : ℤ,
      (scalarBinShiftPairs h m).indicator (fun _ ↦ scalarBinningShiftWeight m) p := by
  let m := scalarBinIndex h p.1 - scalarBinIndex h p.2
  have hp : p ∈ scalarBinShiftPairs h m := by
    apply mem_iUnion.2
    refine ⟨scalarBinIndex h p.1, mem_scalarBin_index hh p.1, ?_⟩
    simpa only [m, sub_sub_cancel] using mem_scalarBin_index hh p.2
  exact (scalarBinningKernel_le_shiftWeight hh p).trans
    (by simpa only [indicator_of_mem hp] using (ENNReal.le_tsum
      (f := fun m ↦ (scalarBinShiftPairs h m).indicator (fun _ ↦ scalarBinningShiftWeight m) p) m))

/-- Lemma 7.3(iii), with the actual double integral and the source constant ten. -/
theorem lintegral_scalarBinningKernel_le_ten (η ζ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ζ] {h : ℝ} (hh : 0 < h) :
    (∫⁻ p, scalarBinningKernel h p ∂η.prod ζ) ≤
      10 * (scalarCollisionMass η η h 0 * scalarCollisionMass ζ ζ h 0) ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ ∫⁻ p, ∑' m : ℤ, (scalarBinShiftPairs h m).indicator
        (fun _ ↦ scalarBinningShiftWeight m) p ∂η.prod ζ :=
      lintegral_mono (scalarBinningKernel_le_tsum_indicators hh)
    _ = ∑' m : ℤ, scalarBinningShiftWeight m * η.prod ζ (scalarBinShiftPairs h m) := by
      rw [lintegral_tsum (fun m ↦ (measurable_const.indicator
        (measurableSet_scalarBinShiftPairs h m)).aemeasurable)]
      apply tsum_congr
      intro m
      rw [lintegral_indicator (measurableSet_scalarBinShiftPairs h m), setLIntegral_const]
    _ ≤ ∑' m : ℤ, scalarBinningShiftWeight m *
        (scalarBinSquareMass η h ^ (1 / 2 : ℝ) * scalarBinSquareMass ζ h ^ (1 / 2 : ℝ)) :=
      ENNReal.tsum_le_tsum fun m ↦ mul_le_mul' le_rfl (measure_scalarBinShiftPairs_le η ζ hh m)
    _ = (∑' m : ℤ, scalarBinningShiftWeight m) *
        (scalarBinSquareMass η h ^ (1 / 2 : ℝ) * scalarBinSquareMass ζ h ^ (1 / 2 : ℝ)) :=
      ENNReal.tsum_mul_right
    _ ≤ 10 * (scalarCollisionMass η η h 0 ^ (1 / 2 : ℝ) *
        scalarCollisionMass ζ ζ h 0 ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul'
      · exact tsum_scalarBinningShiftWeight_le_five.trans (by norm_num)
      · exact mul_le_mul' (ENNReal.rpow_le_rpow (scalarBinSquareMass_le_collision η hh)
          (by norm_num))
          (ENNReal.rpow_le_rpow (scalarBinSquareMass_le_collision ζ hh)
            (by norm_num))
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The iterated-integral form used directly in the source. -/
theorem lintegral_lintegral_scalarBinningKernel_le_ten (η ζ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ζ] {h : ℝ} (hh : 0 < h) :
    (∫⁻ s, ∫⁻ t, ENNReal.ofReal ((1 + |s - t| / h) ^ (-2 : ℝ)) ∂ζ ∂η) ≤
      10 * (scalarCollisionMass η η h 0 * scalarCollisionMass ζ ζ h 0) ^ (1 / 2 : ℝ) := by
  change (∫⁻ s, ∫⁻ t, scalarBinningKernel h (s, t) ∂ζ ∂η) ≤ _
  rw [← lintegral_prod _ (measurable_scalarBinningKernel h).aemeasurable]
  exact lintegral_scalarBinningKernel_le_ten η ζ hh

/-- The actual decaying cross-kernel integral is finite for finite measures. -/
theorem lintegral_scalarBinningKernel_ne_top (η ζ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ζ] {h : ℝ} (hh : 0 < h) :
    (∫⁻ p, scalarBinningKernel h p ∂η.prod ζ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (lintegral_scalarBinningKernel_le_ten η ζ hh)
  unfold scalarCollisionMass
  finiteness

end FalconerThetaGauge
