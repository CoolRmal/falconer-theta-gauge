module

public import FalconerThetaGauge.EqualAngularCellGeometry
public import FalconerThetaGauge.DirectionalTestsPiecesDerivatives

/-! # The literal smooth equal-arc partition for orthogonality -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

def angularPartitionCount (ℓ : ℝ) : ℕ := ⌈2 * Real.pi / ℓ⌉₊

theorem angularPartitionCount_pos {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < angularPartitionCount ℓ := by
  exact Nat.one_le_ceil_iff.mpr (div_pos Real.two_pi_pos hℓ)

theorem equalAngularCellWidth_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    equalAngularCellWidth (angularPartitionCount ℓ) ≤ ℓ := by
  have hM : (0 : ℝ) < angularPartitionCount ℓ := by
    exact_mod_cast angularPartitionCount_pos hℓ
  apply (div_le_iff₀ hM).mpr
  have hh := (div_le_iff₀ hℓ).mp (Nat.le_ceil (2 * Real.pi / ℓ))
  simpa only [angularPartitionCount, mul_comm] using hh

theorem angularPartitionCount_le {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) :
    (angularPartitionCount ℓ : ℝ) ≤ 8 / ℓ := by
  apply (le_div_iff₀ hℓ).mpr
  have hh := mul_lt_mul_of_pos_right
    (Nat.ceil_lt_add_one (div_nonneg Real.two_pi_pos.le hℓ.le)) hℓ
  have he : (2 * Real.pi / ℓ + 1) * ℓ = 2 * Real.pi + ℓ := by field_simp
  rw [he] at hh
  change (⌈2 * Real.pi / ℓ⌉₊ : ℝ) * ℓ ≤ 8
  linarith [Real.pi_lt_d4]

/-- Descend each actual smooth periodic cell convolution to the genuine circle. -/
def equalAngularPartition (K : ℕ) (δ : ℝ) (M : ℕ) (i : Fin M) (w : UnitCircle) : ℝ :=
  equalAngularPartitionLift K δ M i (circleAngle w)

theorem equalAngularPartition_comp_angle (K : ℕ) (δ : ℝ) (M : ℕ) (i : Fin M) (θ : ℝ) :
    equalAngularPartition K δ M i (unitCircleOfAngle θ) = equalAngularPartitionLift K δ M i θ := by
  rw [equalAngularPartition, circleAngle_unitCircleOfAngle]
  exact periodic_apply_toIocMod (equalAngularPartitionLift_periodic K δ M i) θ

theorem equalAngularPartition_mem_Icc (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (M : ℕ) (i : Fin M) (w : UnitCircle) : equalAngularPartition K δ M i w ∈ Set.Icc 0 1 :=
  ⟨smoothIndicator_nonneg K hδ _ _,
    smoothIndicator_le_one K hδ (measurableSet_equalAngularCell M i) _⟩

@[fun_prop]
theorem measurable_equalAngularPartition (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (M : ℕ) (i : Fin M) : Measurable (equalAngularPartition K δ M i) :=
  (contDiff_equalAngularPartitionLift K hδ M i).continuous.measurable.comp measurable_circleAngle

theorem sum_equalAngularPartition {M : ℕ} (hM : 0 < M) (K : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (w : UnitCircle) :
    (∑ i : Fin M, equalAngularPartition K δ M i w) = 1 :=
  sum_equalAngularPartitionLift hM K hδ _

theorem contDiff_equalAngularPartition_comp_angle (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (M : ℕ) (i : Fin M) :
    ContDiff ℝ ∞ (fun θ ↦ equalAngularPartition K δ M i (unitCircleOfAngle θ)) := by
  simp_rw [equalAngularPartition_comp_angle]
  exact contDiff_equalAngularPartitionLift K hδ M i

theorem norm_iteratedDeriv_equalAngularPartition_le {T : ℕ} (M : ℕ) (i : Fin M)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (hk : k ≤ 6 * T) (θ : ℝ) :
    ‖iteratedDeriv k
      (fun θ ↦ equalAngularPartition (6 * T) (ℓ / 2) M i (unitCircleOfAngle θ)) θ‖ ≤
      (576 * (T : ℝ) ^ 2 / ℓ) ^ k := by
  simp_rw [equalAngularPartition_comp_angle]
  have hδ : 0 < ℓ / 2 := by positivity
  have hpi : Real.pi ^ 2 / 6 ≤ 3 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  calc
    _ ≤ (ℓ / 2)⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) :=
      norm_iteratedDeriv_smoothIndicator_le_explicit (6 * T) k hk hδ
        (measurableSet_equalAngularCell M i) θ
    _ ≤ (ℓ / 2)⁻¹ ^ k * (3 ^ k * ((6 * (T : ℝ)) ^ k) ^ 2) := by
      gcongr
      exact factorial_cast_le_cutoff_order_pow hk
    _ = ((ℓ / 2)⁻¹ * (3 * (6 * (T : ℝ)) ^ 2)) ^ k := by
      have hp : ((6 * (T : ℝ)) ^ k) ^ 2 = ((6 * (T : ℝ)) ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      rw [hp, ← mul_pow, ← mul_pow]
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      have he : (ℓ / 2)⁻¹ * (3 * (6 * (T : ℝ)) ^ 2) = 216 * (T : ℝ) ^ 2 / ℓ := by
        field_simp
        ring
      rw [he]
      gcongr
      norm_num

/-- The actual smoothed arc can only contribute within the literal angular localization radius. -/
theorem equalAngularPartition_norm_sub_center_le (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i : Fin (angularPartitionCount ℓ)) {w : UnitCircle}
    (hw : equalAngularPartition K (ℓ / 2) (angularPartitionCount ℓ) i w ≠ 0) :
    ‖(w : Plane) - (unitCircleOfAngle
      (equalAngularCellCenter (angularPartitionCount ℓ) i) : Plane)‖ ≤ ℓ := by
  have hs : circleAngle w ∈ tsupport
      (equalAngularPartitionLift K (ℓ / 2) (angularPartitionCount ℓ) i) := subset_closure hw
  have hmem := tsupport_equalAngularPartitionLift_subset (angularPartitionCount_pos hℓ)
    K (by positivity : 0 < ℓ / 2) i hs
  have hmem' : w ∈ closedArcNeighborhood (ℓ / 2)
      (closedDirectionArc (equalAngularCellCenter (angularPartitionCount ℓ) i)
        (equalAngularCellWidth (angularPartitionCount ℓ) / 2)) := by
    simpa only [angularPassingSet, Set.mem_preimage, unitCircleOfAngle_circleAngle] using hmem
  have hb := norm_sub_le_of_mem_closedArcNeighborhood (by positivity : 0 ≤ ℓ / 2)
    (fun z hz ↦ norm_sub_le_of_mem_closedDirectionArc _ hz) hmem'
  have hwid := equalAngularCellWidth_le hℓ
  linarith

/-- Each genuine arc cutoff satisfies the source's uniform `576T²/ℓ` derivative scale. -/
theorem equalAngularPartition_isDerivativeRegular {T : ℕ} (hT : 1 ≤ T)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (M : ℕ) (i : Fin M) :
    IsDerivativeRegular 1 (576 * (T : ℝ) ^ 2 / ℓ) (6 * T)
      (fun θ ↦ (equalAngularPartition (6 * T) (ℓ / 2) M i (unitCircleOfAngle θ) : ℂ)) := by
  have hf := contDiff_equalAngularPartition_comp_angle (6 * T)
    (by positivity : 0 < ℓ / 2) M i
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hscale : 1 ≤ 576 * (T : ℝ) ^ 2 / ℓ := by
    apply (le_div_iff₀ hℓ).mpr
    nlinarith
  refine ⟨by norm_num, hscale, (Complex.ofRealCLM.contDiff.comp hf).of_le
    (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) (6 * T)), ?_⟩
  intro k hk θ
  rw [iteratedDeriv_ofReal_eq ((hf.of_le (by simp)).contDiffAt)]
  simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
    norm_iteratedDeriv_equalAngularPartition_le M i hℓ hk θ

end FalconerThetaGauge
