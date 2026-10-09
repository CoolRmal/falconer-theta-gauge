module

public import FalconerThetaGauge.DirectionalTestsMarkov
public import FalconerThetaGauge.RegularMeasureExcessCount
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # The actual finite occupied-cell tube count in Definition 6.2 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- The true center of the manuscript's half-open generation-`p` dyadic cell. -/
def dyadicCellCenter (p : ℕ) (k : Fin 2 → ℤ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i ↦ ((k i : ℝ) + 1 / 2) / (2 : ℝ) ^ p)

/-- Precisely the finite occupied cells of the actual measure in the unit square. -/
def occupiedUnitCells (ρ : Measure Plane) (p : ℕ) : Finset (Fin 2 → ℤ) :=
  (unitCellIndices p).filter (fun k ↦ 0 < unitCellWeight ρ p k)

/-- The residual from orthogonal projection onto the true affine line `c + ℝw`. -/
def directionLineResidual (c : Plane) (w : UnitCircle) (z : Plane) : Plane :=
  z - c - inner ℝ (w : Plane) (z - c) • (w : Plane)

@[fun_prop]
theorem continuous_directionLineResidual (c z : Plane) :
    Continuous (fun w : UnitCircle ↦ directionLineResidual c w z) := by
  unfold directionLineResidual
  fun_prop

theorem directionLineResidual_antipodal (c z : Plane) (w : UnitCircle) :
    directionLineResidual c (circleAntipode w) z = directionLineResidual c w z := by
  simp [directionLineResidual, inner_neg_left, neg_smul, smul_neg]

theorem directionLineResidual_norm_le (c z : Plane) (w : UnitCircle) (t : ℝ) :
    ‖directionLineResidual c w z‖ ≤ ‖z - c - t • (w : Plane)‖ := by
  have hw : ‖(w : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  have hsq : ∀ a : ℝ, ‖z - c - a • (w : Plane)‖ ^ 2 =
      ‖z - c‖ ^ 2 - 2 * a * inner ℝ (w : Plane) (z - c) + a ^ 2 := by
    intro a
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm (z - c),
      norm_smul, hw, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have h0 := hsq (inner ℝ (w : Plane) (z - c))
  have h1 := hsq t
  change ‖z - c - inner ℝ (w : Plane) (z - c) • (w : Plane)‖ ≤ _
  nlinarith [sq_nonneg (t - inner ℝ (w : Plane) (z - c)),
    norm_nonneg (z - c - inner ℝ (w : Plane) (z - c) • (w : Plane)),
    norm_nonneg (z - c - t • (w : Plane))]

/-- The residual formula is precisely the Euclidean distance to the true affine line. -/
theorem infDist_directionLine_eq_residual (c z : Plane) (w : UnitCircle) :
    Metric.infDist z (Set.range (fun t : ℝ ↦ c + t • (w : Plane))) =
      ‖directionLineResidual c w z‖ := by
  apply le_antisymm
  · have hm : c + inner ℝ (w : Plane) (z - c) • (w : Plane) ∈
        Set.range (fun t : ℝ ↦ c + t • (w : Plane)) := ⟨_, rfl⟩
    simpa only [dist_eq_norm, sub_add_eq_sub_sub, directionLineResidual] using
      Metric.infDist_le_dist_of_mem (x := z) hm
  · apply (Metric.le_infDist (Set.range_nonempty _)).mpr
    rintro y ⟨t, rfl⟩
    simpa only [dist_eq_norm, sub_add_eq_sub_sub] using directionLineResidual_norm_le c z w t

/-- The closed tube at the literal radii and width of Definition 6.2; `E=εN`. -/
def directionalTube (g p : ℕ) (E width : ℝ) (c : Plane) (w : UnitCircle) : Set Plane :=
  {z | ‖directionLineResidual c w z‖ ≤ width * (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E) ∧
    ‖z - c‖ ≤ 4 * (2 : ℝ) ^ (-(g : ℝ))}

theorem measurableSet_tubeCellDirections (g p : ℕ) (E width : ℝ) (c z : Plane) :
    MeasurableSet {w : UnitCircle | z ∈ directionalTube g p E width c w} := by
  exact ((isClosed_le (continuous_directionLineResidual c z).norm continuous_const).inter
    (isClosed_const : IsClosed {w : UnitCircle | ‖z - c‖ ≤ 4 * (2 : ℝ) ^ (-(g : ℝ))})).measurableSet

/-- The true number of occupied generation-`p` cell centers in the closed tube. -/
def tubeCount (ρ : Measure Plane) (g p : ℕ) (E width : ℝ) (P : Fin 2 → ℤ) :
    UnitCircle → ℝ :=
  fun w ↦ ∑ Q ∈ occupiedUnitCells ρ p,
    {w : UnitCircle | dyadicCellCenter p Q ∈
      directionalTube g p E width (dyadicCellCenter p P) w}.indicator (fun _ ↦ 1) w

theorem measurable_tubeCount (ρ : Measure Plane) (g p : ℕ) (E width : ℝ) (P : Fin 2 → ℤ) :
    Measurable (tubeCount ρ g p E width P) := by
  apply (occupiedUnitCells ρ p).measurable_sum
  intro Q _
  exact measurable_const.indicator (measurableSet_tubeCellDirections g p E width _ _)

theorem tubeCount_nonneg (ρ : Measure Plane) (g p : ℕ) (E width : ℝ) (P : Fin 2 → ℤ)
    (w : UnitCircle) : 0 ≤ tubeCount ρ g p E width P w := by
  apply Finset.sum_nonneg
  intro Q _
  simp only [indicator]
  split_ifs <;> norm_num

theorem tubeCount_le_card (ρ : Measure Plane) (g p : ℕ) (E width : ℝ) (P : Fin 2 → ℤ)
    (w : UnitCircle) : tubeCount ρ g p E width P w ≤ (occupiedUnitCells ρ p).card := by
  calc
    _ ≤ ∑ _Q ∈ occupiedUnitCells ρ p, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro Q _
      simp only [indicator]
      split_ifs <;> norm_num
    _ = _ := by simp

theorem integrable_tubeCount (ρ : Measure Plane) (g p : ℕ) (E width : ℝ) (P : Fin 2 → ℤ) :
    Integrable (tubeCount ρ g p E width P) circleArcLength :=
  Integrable.of_bound (measurable_tubeCount ρ g p E width P).aestronglyMeasurable
    (occupiedUnitCells ρ p).card (Filter.Eventually.of_forall (fun w ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (tubeCount_nonneg ρ g p E width P w)]
      exact tubeCount_le_card ρ g p E width P w))

theorem tubeCount_antipodal (ρ : Measure Plane) (g p : ℕ) (E width : ℝ) (P : Fin 2 → ℤ)
    (w : UnitCircle) :
    tubeCount ρ g p E width P (circleAntipode w) = tubeCount ρ g p E width P w := by
  apply Finset.sum_congr rfl
  intro Q _
  have heq : dyadicCellCenter p Q ∈ directionalTube g p E width (dyadicCellCenter p P)
      (circleAntipode w) ↔
      dyadicCellCenter p Q ∈ directionalTube g p E width (dyadicCellCenter p P) w := by
    simp only [directionalTube, mem_ofPred_eq, directionLineResidual_antipodal]
  simp only [indicator, mem_ofPred_eq, heq]

theorem directionalTube_mono_width (g p : ℕ) (E : ℝ) {width width' : ℝ} (hwidth : width ≤ width')
    (c : Plane) (w : UnitCircle) :
    directionalTube g p E width c w ⊆ directionalTube g p E width' c w := by
  intro z hz
  exact ⟨hz.1.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hwidth (by positivity)) (by positivity)), hz.2⟩

theorem tubeCount_mono_width (ρ : Measure Plane) (g p : ℕ) (E : ℝ) {width width' : ℝ}
    (hwidth : width ≤ width') (P : Fin 2 → ℤ) (w : UnitCircle) :
    tubeCount ρ g p E width P w ≤ tubeCount ρ g p E width' P w := by
  apply Finset.sum_le_sum
  intro Q _
  simp only [indicator, mem_ofPred_eq]
  by_cases hw : dyadicCellCenter p Q ∈ directionalTube g p E width (dyadicCellCenter p P) w
  · simp only [ite_eq_left hw,
      ite_eq_left (directionalTube_mono_width g p E hwidth _ _ hw), le_refl]
  · rw [ite_eq_right hw]
    split_ifs <;> norm_num

/-- The source's width-2 actual tube average. -/
def tubeAverage (ρ : Measure Plane) (g p : ℕ) (E : ℝ) (P : Fin 2 → ℤ) : ℝ :=
  directionalAverage (tubeCount ρ g p E 2 P)

/-- The literal passing inequality at any width, against the width-2 average. -/
def tubePassingDirections (ρ : Measure Plane) (g p : ℕ) (E width : ℝ) (P : Fin 2 → ℤ) :
    Set UnitCircle := {w | tubeCount ρ g p E width P w ≤ (2 : ℝ) ^ (2 * E) * tubeAverage ρ g p E P}

theorem circleArcLength_tube_failure_le (ρ : Measure Plane) (g p : ℕ) (E : ℝ)
    (P : Fin 2 → ℤ) :
    circleArcLength (tubePassingDirections ρ g p E 2 P)ᶜ ≤
      ENNReal.ofReal (2 * Real.pi * (2 : ℝ) ^ (-2 * E)) := by
  have h := circleArcLength_directionalTestFailure_le (q := (2 : ℝ) ^ (2 * E))
    (Real.rpow_pos_of_pos (by norm_num) _)
    (integrable_tubeCount ρ g p E 2 P) (tubeCount_nonneg ρ g p E 2 P)
  have heq : (tubePassingDirections ρ g p E 2 P)ᶜ =
      directionalTestFailure ((2 : ℝ) ^ (2 * E)) (tubeCount ρ g p E 2 P) := by
    ext w
    simp only [tubePassingDirections, directionalTestFailure, mem_compl_iff,
      mem_ofPred_eq, not_le, tubeAverage]
  rw [heq]
  convert h using 1
  rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [neg_mul]

end FalconerThetaGauge
