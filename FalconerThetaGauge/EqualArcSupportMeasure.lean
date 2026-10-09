module

public import FalconerThetaGauge.EqualArcCutoff

/-! # True support length of a smoothed arc within the period centered on that arc -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

theorem abs_angle_sub_le_of_small_chord {θ α ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1)
    (hθ : |θ - α| ≤ Real.pi)
    (hc : ‖angularDirection θ - angularDirection α‖ ≤ 3 * ℓ / 4) : |θ - α| ≤ ℓ := by
  rw [norm_angularDirection_sub_eq, Real.norm_eq_abs, abs_mul, Nat.abs_ofNat] at hc
  have hab : |(θ - α) / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hab, abs_div, Nat.abs_ofNat] at hc
  by_contra h
  have hlt : ℓ < |θ - α| := lt_of_not_ge h
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (x := ℓ / 2) (y := |θ - α| / 2) (by linarith [Real.pi_pos])
    (by linarith) (by linarith)
  have hlo := Real.sin_ge_sub_cube (x := ℓ / 2) (by positivity)
  have hsquare : ℓ ^ 2 ≤ 1 := by nlinarith
  have hcube : ℓ ^ 3 ≤ ℓ := by
    have hh := mul_le_mul_of_nonneg_right hsquare hℓ.le
    nlinarith
  nlinarith

theorem equalArcCutoff_support_chord_le (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) {θ : ℝ}
    (hθ : θ ∈ tsupport (fun t ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle t))) :
    ‖angularDirection θ - angularDirection
      (equalAngularCellCenter (angularPartitionCount ℓ) arc)‖ ≤ 3 * ℓ / 4 := by
  let w := equalAngularCellWidth (angularPartitionCount ℓ)
  have he : (fun t ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle t)) =
      equalAngularPartitionLift K (w / 4) (angularPartitionCount ℓ) arc := by
    funext t
    exact equalAngularPartition_comp_angle K (w / 4) _ arc t
  rw [he] at hθ
  have hmem := tsupport_equalAngularPartitionLift_subset (angularPartitionCount_pos hℓ)
    K (equalArcCutoff_scale_pos hℓ) arc hθ
  have hw : unitCircleOfAngle θ ∈ closedArcNeighborhood (w / 4)
      (closedDirectionArc (equalAngularCellCenter (angularPartitionCount ℓ) arc) (w / 2)) :=
    hmem
  have hc := norm_sub_le_of_mem_closedArcNeighborhood (equalArcCutoff_scale_pos hℓ).le
    (fun z hz ↦ norm_sub_le_of_mem_closedDirectionArc _ hz) hw
  have hwidth := equalAngularCellWidth_le hℓ
  change ‖angularDirection θ - angularDirection
    (equalAngularCellCenter (angularPartitionCount ℓ) arc)‖ ≤ _ at hc
  dsimp [w] at hc
  linarith

theorem equalArcCutoff_support_period_subset (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓ₁ : ℓ ≤ 1) (arc : Fin (angularPartitionCount ℓ)) :
    tsupport (fun θ ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle θ)) ∩
      Ioc (equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi)
        (equalAngularCellCenter (angularPartitionCount ℓ) arc + Real.pi) ⊆
      Icc (equalAngularCellCenter (angularPartitionCount ℓ) arc - ℓ)
        (equalAngularCellCenter (angularPartitionCount ℓ) arc + ℓ) := by
  intro θ hθ
  have hc := equalArcCutoff_support_chord_le K hℓ arc hθ.1
  have hangle : |θ - equalAngularCellCenter (angularPartitionCount ℓ) arc| ≤ Real.pi :=
    abs_le.mpr ⟨by linarith [hθ.2.1], by linarith [hθ.2.2]⟩
  have hsmall := abs_le.mp (abs_angle_sub_le_of_small_chord hℓ hℓ₁ hangle hc)
  exact ⟨by linarith [hsmall.1], by linarith [hsmall.2]⟩

theorem equalArcCutoff_support_period_mass_le (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓ₁ : ℓ ≤ 1) (arc : Fin (angularPartitionCount ℓ)) :
    volume.real (tsupport (fun θ ↦ equalArcCutoff K ℓ arc (unitCircleOfAngle θ)) ∩
      Ioc (equalAngularCellCenter (angularPartitionCount ℓ) arc - Real.pi)
        (equalAngularCellCenter (angularPartitionCount ℓ) arc + Real.pi)) ≤ 2 * ℓ := by
  have h := ENNReal.toReal_mono (by simp : volume
      (Icc (equalAngularCellCenter (angularPartitionCount ℓ) arc - ℓ)
        (equalAngularCellCenter (angularPartitionCount ℓ) arc + ℓ)) ≠ ⊤)
    (measure_mono (equalArcCutoff_support_period_subset K hℓ hℓ₁ arc))
  have hlen : (equalAngularCellCenter (angularPartitionCount ℓ) arc + ℓ) -
      (equalAngularCellCenter (angularPartitionCount ℓ) arc - ℓ) = 2 * ℓ := by ring
  rw [Real.volume_Icc, hlen, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ℓ)] at h
  exact h

end FalconerThetaGauge
