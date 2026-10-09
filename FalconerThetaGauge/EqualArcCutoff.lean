module

public import FalconerThetaGauge.EqualAngularPartition

/-! # The equal arcs smoothed at one quarter of their actual width -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

theorem equalAngularCellWidth_lower {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) :
    ℓ / 2 ≤ equalAngularCellWidth (angularPartitionCount ℓ) := by
  have hM : (0 : ℝ) < angularPartitionCount ℓ := by
    exact_mod_cast angularPartitionCount_pos hℓ
  apply (le_div_iff₀ hM).mpr
  have hh := mul_lt_mul_of_pos_right
    (Nat.ceil_lt_add_one (div_nonneg Real.two_pi_pos.le hℓ.le)) hℓ
  have he : (2 * Real.pi / ℓ + 1) * ℓ = 2 * Real.pi + ℓ := by field_simp
  rw [he] at hh
  change ℓ / 2 * (⌈2 * Real.pi / ℓ⌉₊ : ℝ) ≤ 2 * Real.pi
  nlinarith [Real.pi_gt_three]

/-- The source's literal convolution `1_A * ω_(|A|/4)` on each periodic equal arc. -/
def equalArcCutoff (K : ℕ) (ℓ : ℝ) (i : Fin (angularPartitionCount ℓ))
    (w : UnitCircle) : ℝ :=
  equalAngularPartition K (equalAngularCellWidth (angularPartitionCount ℓ) / 4)
    (angularPartitionCount ℓ) i w

theorem equalArcCutoff_scale_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 < equalAngularCellWidth (angularPartitionCount ℓ) / 4 := by
  have hM : (0 : ℝ) < angularPartitionCount ℓ := by
    exact_mod_cast angularPartitionCount_pos hℓ
  exact div_pos (div_pos Real.two_pi_pos hM) (by norm_num)

theorem equalArcCutoff_mem_Icc (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i : Fin (angularPartitionCount ℓ)) (w : UnitCircle) :
    equalArcCutoff K ℓ i w ∈ Set.Icc 0 1 :=
  equalAngularPartition_mem_Icc K (equalArcCutoff_scale_pos hℓ) _ i w

@[fun_prop]
theorem measurable_equalArcCutoff (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i : Fin (angularPartitionCount ℓ)) : Measurable (equalArcCutoff K ℓ i) :=
  measurable_equalAngularPartition K (equalArcCutoff_scale_pos hℓ) _ i

theorem sum_equalArcCutoff (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (w : UnitCircle) :
    (∑ i : Fin (angularPartitionCount ℓ), equalArcCutoff K ℓ i w) = 1 :=
  sum_equalAngularPartition (angularPartitionCount_pos hℓ) K
    (equalArcCutoff_scale_pos hℓ) w

theorem contDiff_equalArcCutoff_comp_angle (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i : Fin (angularPartitionCount ℓ)) :
    ContDiff ℝ ∞ (fun θ ↦ equalArcCutoff K ℓ i (unitCircleOfAngle θ)) :=
  contDiff_equalAngularPartition_comp_angle K (equalArcCutoff_scale_pos hℓ) _ i

theorem equalArcCutoff_norm_sub_center_le (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i : Fin (angularPartitionCount ℓ)) {w : UnitCircle}
    (hw : equalArcCutoff K ℓ i w ≠ 0) :
    ‖(w : Plane) - (unitCircleOfAngle
      (equalAngularCellCenter (angularPartitionCount ℓ) i) : Plane)‖ ≤ ℓ := by
  let δ := equalAngularCellWidth (angularPartitionCount ℓ) / 4
  have hδ : 0 < δ := equalArcCutoff_scale_pos hℓ
  have hs : circleAngle w ∈ tsupport
      (equalAngularPartitionLift K δ (angularPartitionCount ℓ) i) := subset_closure hw
  have hmem := tsupport_equalAngularPartitionLift_subset (angularPartitionCount_pos hℓ)
    K hδ i hs
  have hmem' : w ∈ closedArcNeighborhood δ
      (closedDirectionArc (equalAngularCellCenter (angularPartitionCount ℓ) i)
        (equalAngularCellWidth (angularPartitionCount ℓ) / 2)) := by
    simpa only [angularPassingSet, Set.mem_preimage, unitCircleOfAngle_circleAngle] using hmem
  have hb := norm_sub_le_of_mem_closedArcNeighborhood hδ.le
    (fun z hz ↦ norm_sub_le_of_mem_closedDirectionArc _ hz) hmem'
  have hwid := equalAngularCellWidth_le hℓ
  have hwid₀ := (equalArcCutoff_scale_pos hℓ).le
  dsimp [δ] at hb
  change ‖(w : Plane) - angularDirection
    (equalAngularCellCenter (angularPartitionCount ℓ) i)‖ ≤ ℓ
  linarith

theorem norm_iteratedDeriv_equalArcCutoff_le {T : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (i : Fin (angularPartitionCount ℓ))
    {k : ℕ} (hk : k ≤ 6 * T) (θ : ℝ) :
    ‖iteratedDeriv k (fun θ ↦
      equalArcCutoff (6 * T) ℓ i (unitCircleOfAngle θ)) θ‖ ≤
      (576 * (T : ℝ) ^ 2 / ℓ) ^ k := by
  unfold equalArcCutoff
  simp_rw [equalAngularPartition_comp_angle]
  let w := equalAngularCellWidth (angularPartitionCount ℓ)
  have hw : 0 < w := by
    have hh := equalArcCutoff_scale_pos hℓ
    dsimp [w]
    linarith
  have hlo : ℓ / 2 ≤ w := equalAngularCellWidth_lower hℓ hℓ₁
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  calc
    _ ≤ (w / 4)⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) :=
      norm_iteratedDeriv_smoothIndicator_le_explicit (6 * T) k hk (by positivity)
        (measurableSet_equalAngularCell _ i) θ
    _ ≤ (w / 4)⁻¹ ^ k * (2 ^ k * ((6 * (T : ℝ)) ^ k) ^ 2) := by
      gcongr
      exact factorial_cast_le_cutoff_order_pow hk
    _ = ((w / 4)⁻¹ * (2 * (6 * (T : ℝ)) ^ 2)) ^ k := by
      have hp : ((6 * (T : ℝ)) ^ k) ^ 2 = ((6 * (T : ℝ)) ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      rw [hp, ← mul_pow, ← mul_pow]
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      have he : (w / 4)⁻¹ * (2 * (6 * (T : ℝ)) ^ 2) =
          288 * (T : ℝ) ^ 2 / w := by field_simp; ring
      rw [he]
      apply (div_le_div_iff₀ hw hℓ).mpr
      nlinarith [sq_nonneg (T : ℝ), mul_nonneg
        (sq_nonneg (T : ℝ)) (sub_nonneg.mpr hlo)]

theorem equalArcCutoff_isDerivativeRegular {T : ℕ} (hT : 1 ≤ T)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (i : Fin (angularPartitionCount ℓ)) :
    IsDerivativeRegular 1 (576 * (T : ℝ) ^ 2 / ℓ) (6 * T)
      (fun θ ↦ (equalArcCutoff (6 * T) ℓ i (unitCircleOfAngle θ) : ℂ)) := by
  have hf := contDiff_equalArcCutoff_comp_angle (6 * T) hℓ i
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hscale : 1 ≤ 576 * (T : ℝ) ^ 2 / ℓ := by
    apply (le_div_iff₀ hℓ).mpr
    nlinarith
  refine ⟨by norm_num, hscale, (Complex.ofRealCLM.contDiff.comp hf).of_le
    (ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) (6 * T)), ?_⟩
  intro k hk θ
  rw [iteratedDeriv_ofReal_eq ((hf.of_le (by simp)).contDiffAt)]
  simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
    norm_iteratedDeriv_equalArcCutoff_le hℓ hℓ₁ i hk θ

end FalconerThetaGauge
