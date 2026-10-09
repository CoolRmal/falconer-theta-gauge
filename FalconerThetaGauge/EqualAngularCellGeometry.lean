module

public import FalconerThetaGauge.EqualAngularCells
public import FalconerThetaGauge.SeparatedDirectionsNeighborhood

/-! # Literal centers and support geometry of the equal angular cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

def equalAngularCellWidth (M : ℕ) : ℝ := 2 * Real.pi / M

def equalAngularCellCenter (M : ℕ) (i : Fin M) : ℝ :=
  ((i.val : ℝ) + 1 / 2) * equalAngularCellWidth M

theorem unitCircleOfAngle_angularFundamentalCoordinate (θ : ℝ) :
    unitCircleOfAngle (angularFundamentalCoordinate θ) = unitCircleOfAngle θ := by
  have hp : Periodic unitCircleOfAngle (2 * Real.pi) := unitCircleOfAngle_add_two_pi
  have he := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 θ
  rw [zsmul_eq_mul] at he
  calc
    _ = unitCircleOfAngle (angularFundamentalCoordinate θ +
        (toIcoDiv Real.two_pi_pos 0 θ : ℝ) * (2 * Real.pi)) :=
      ((hp.int_mul (toIcoDiv Real.two_pi_pos 0 θ)) (angularFundamentalCoordinate θ)).symm
    _ = _ := congrArg unitCircleOfAngle he

theorem equalAngularCell_coordinate_bounds {M : ℕ} (hM : 0 < M) (i : Fin M)
    {θ : ℝ} (hθ : θ ∈ equalAngularCell M i) :
    angularFundamentalCoordinate θ ∈ Ico ((i.val : ℝ) * equalAngularCellWidth M)
      (((i.val : ℝ) + 1) * equalAngularCellWidth M) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hw : 0 < equalAngularCellWidth M := div_pos Real.two_pi_pos hMR
  have hlo := Nat.floor_le (angularCellCoordinate_nonneg M θ)
  have hhi := Nat.lt_floor_add_one ((M : ℝ) * angularFundamentalCoordinate θ / (2 * Real.pi))
  change ⌊(M : ℝ) * angularFundamentalCoordinate θ / (2 * Real.pi)⌋₊ = i.val at hθ
  rw [hθ] at hlo hhi
  have he : ((M : ℝ) * angularFundamentalCoordinate θ / (2 * Real.pi)) *
      equalAngularCellWidth M = angularFundamentalCoordinate θ := by
    unfold equalAngularCellWidth
    field_simp
  constructor
  · simpa only [he] using mul_le_mul_of_nonneg_right hlo hw.le
  · simpa only [he] using mul_lt_mul_of_pos_right hhi hw

theorem equalAngularCell_mem_closedDirectionArc {M : ℕ} (hM : 0 < M) (i : Fin M)
    {θ : ℝ} (hθ : θ ∈ equalAngularCell M i) :
    unitCircleOfAngle θ ∈ closedDirectionArc (equalAngularCellCenter M i)
      (equalAngularCellWidth M / 2) := by
  have hb := equalAngularCell_coordinate_bounds hM i hθ
  refine ⟨angularFundamentalCoordinate θ, ?_, unitCircleOfAngle_angularFundamentalCoordinate θ⟩
  unfold equalAngularCellCenter
  constructor <;> linarith [hb.1, hb.2]

theorem tsupport_equalAngularPartitionLift_subset {M : ℕ} (hM : 0 < M)
    (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (i : Fin M) :
    tsupport (equalAngularPartitionLift K δ M i) ⊆
      angularPassingSet (closedArcNeighborhood δ
        (closedDirectionArc (equalAngularCellCenter M i) (equalAngularCellWidth M / 2))) := by
  rw [angularPassingSet_closedArcNeighborhood]
  apply (tsupport_smoothIndicator_subset_cthickening K hδ _).trans
  apply Metric.cthickening_subset_of_subset δ
  intro θ hθ
  exact equalAngularCell_mem_closedDirectionArc hM i hθ

end FalconerThetaGauge
