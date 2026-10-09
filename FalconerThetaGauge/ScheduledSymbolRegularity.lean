module

public import FalconerThetaGauge.ScheduledSymbolExpansion

/-! # The full S3 derivative regularity of actual built scheduled symbols -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem one_le_scheduledSymbolScale {T : ℕ} (hT : 1 ≤ T) (E : ℝ)
    (I : Finset ProfileScheduleTest) (hI : I.Nonempty) (L : ℕ) :
    1 ≤ scheduledSymbolScale T E I L := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hc : (1 : ℝ) ≤ I.card := by exact_mod_cast Finset.card_pos.2 hI
  have hm : 1 ≤ max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) := le_max_left _ _
  unfold scheduledSymbolScale
  calc
    1 ≤ 128 * (T : ℝ) ^ 2 * I.card * 1 := by nlinarith [sq_nonneg (T : ℝ)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

theorem ScheduledSymbolData.abs_iteratedDeriv_symbol_le (d : ScheduledSymbolData)
    (ρ : Measure Plane) {T : ℕ} (E width : ℝ) (I : Finset ProfileScheduleTest)
    {L : ℕ} (hL : ∀ test ∈ I, test.length ≤ L) (j : ℕ)
    (horder : d.order I + j ≤ 8 * T) (x : Plane) (θ : ℝ) :
    |iteratedDeriv j (fun t ↦ d.symbol ρ E width (8 * T) I x (unitCircleOfAngle t)) θ| ≤
      scheduledSymbolScale T E I L ^ j := by
  rw [d.iteratedDeriv_symbol_eq]
  calc
    _ ≤ ∑ b : ScheduledSymbolBranch I j, |d.branchCoefficient E I j b *
        (d.branchData I j b).symbol ρ E width (8 * T) I x (unitCircleOfAngle θ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : ScheduledSymbolBranch I j, |d.branchCoefficient E I j b| := by
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        ((d.branchData I j b).abs_symbol_le_one ρ E width (8 * T) I
          (by simpa only [d.branchData_order] using horder) x (unitCircleOfAngle θ))
    _ ≤ _ := d.sum_abs_branchCoefficients_le E I hL j horder

/-- Source S3, with the literal class witnesses and the exact scale `M_L`. -/
theorem ScheduledSymbolData.isDerivativeRegular (d : ScheduledSymbolData)
    (ρ : Measure Plane) {T : ℕ} (hT : 1 ≤ T) (E width : ℝ)
    (I : Finset ProfileScheduleTest) (hI : I.Nonempty) {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) (horder : d.order I ≤ 2 * T) (x : Plane) :
    IsDerivativeRegular 1 (scheduledSymbolScale T E I L) (6 * T)
      (fun θ ↦ (d.symbol ρ E width (8 * T) I x (unitCircleOfAngle θ) : ℂ)) := by
  have hf := d.contDiff_symbol_comp_angle ρ E width (8 * T) I x
  refine ⟨by norm_num, one_le_scheduledSymbolScale hT E I hI L,
    (Complex.ofRealCLM.contDiff.comp hf).of_le
      (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) (6 * T)), ?_⟩
  intro j hj θ
  rw [iteratedDeriv_ofReal_eq ((hf.of_le (by simp)).contDiffAt)]
  simp only [Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact d.abs_iteratedDeriv_symbol_le ρ E width I hL j (by omega) x θ

theorem isDerivativeRegular_of_mem_scheduledSymbolClass (ρ : Measure Plane) {T : ℕ}
    (hT : 1 ≤ T) (E width : ℝ) (I : Finset ProfileScheduleTest) (hI : I.Nonempty)
    {L : ℕ} (hL : ∀ test ∈ I, test.length ≤ L) {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width (8 * T) I (2 * T)) (x : Plane) :
    IsDerivativeRegular 1 (scheduledSymbolScale T E I L) (6 * T)
      (fun θ ↦ (b x (unitCircleOfAngle θ) : ℂ)) := by
  obtain ⟨d, horder, rfl⟩ := hb
  exact d.isDerivativeRegular ρ hT E width I hI hL horder x

end FalconerThetaGauge
