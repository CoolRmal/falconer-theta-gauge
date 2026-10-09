module

public import FalconerThetaGauge.SmoothAngularPartition
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # The actual equal half-open angular cells and their smooth partition -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerThetaGauge

def angularFundamentalCoordinate (θ : ℝ) : ℝ := toIcoMod Real.two_pi_pos 0 θ

def equalAngularCell (M : ℕ) (i : Fin M) : Set ℝ :=
  {θ | ⌊(M : ℝ) * angularFundamentalCoordinate θ / (2 * Real.pi)⌋₊ = i.val}

theorem angularFundamentalCoordinate_bounds (θ : ℝ) :
    angularFundamentalCoordinate θ ∈ Ico 0 (2 * Real.pi) :=
  toIcoMod_mem_Ico' Real.two_pi_pos θ

theorem angularCellCoordinate_nonneg (M : ℕ) (θ : ℝ) :
    0 ≤ (M : ℝ) * angularFundamentalCoordinate θ / (2 * Real.pi) :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (angularFundamentalCoordinate_bounds θ).1)
    (by positivity)

theorem angularCellCoordinate_lt {M : ℕ} (hM : 0 < M) (θ : ℝ) :
    (M : ℝ) * angularFundamentalCoordinate θ / (2 * Real.pi) < M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_lt_iff₀ Real.two_pi_pos]
  exact mul_lt_mul_of_pos_left (angularFundamentalCoordinate_bounds θ).2 hMR

theorem equalAngularCells_partition {M : ℕ} (hM : 0 < M) (θ : ℝ) :
    ∃! i : Fin M, θ ∈ equalAngularCell M i := by
  let q := (M : ℝ) * angularFundamentalCoordinate θ / (2 * Real.pi)
  have hq : ⌊q⌋₊ < M := (Nat.floor_lt (angularCellCoordinate_nonneg M θ)).mpr
    (angularCellCoordinate_lt hM θ)
  refine ⟨⟨⌊q⌋₊, hq⟩, rfl, ?_⟩
  intro i hi
  apply Fin.ext
  exact hi.symm

theorem equalAngularCell_periodic (M : ℕ) (i : Fin M) (θ : ℝ) :
    θ + 2 * Real.pi ∈ equalAngularCell M i ↔ θ ∈ equalAngularCell M i := by
  simp only [equalAngularCell, mem_ofPred_eq, angularFundamentalCoordinate,
    toIcoMod_add_right]

@[fun_prop]
theorem measurable_angularFundamentalCoordinate : Measurable angularFundamentalCoordinate := by
  have he : angularFundamentalCoordinate = fun θ : ℝ ↦
      Int.fract (θ / (2 * Real.pi)) * (2 * Real.pi) := by
    funext θ
    exact toIcoMod_eq_fract_mul Real.two_pi_pos θ
  rw [he]
  exact (measurable_id.div_const (2 * Real.pi)).fract.mul_const _

theorem measurableSet_equalAngularCell (M : ℕ) (i : Fin M) :
    MeasurableSet (equalAngularCell M i) := by
  apply measurableSet_eq_fun
  · exact ((measurable_angularFundamentalCoordinate.const_mul (M : ℝ)).div_const
      (2 * Real.pi)).nat_floor
  · exact measurable_const

def equalAngularPartitionLift (K : ℕ) (δ : ℝ) (M : ℕ) (i : Fin M) : ℝ → ℝ :=
  smoothIndicator K δ (equalAngularCell M i)

theorem sum_equalAngularPartitionLift {M : ℕ} (hM : 0 < M) (K : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) :
    (∑ i : Fin M, equalAngularPartitionLift K δ M i θ) = 1 :=
  sum_smoothIndicator_partition _ (measurableSet_equalAngularCell M)
    (equalAngularCells_partition hM) K hδ θ

theorem equalAngularPartitionLift_periodic (K : ℕ) (δ : ℝ) (M : ℕ) (i : Fin M) :
    Periodic (equalAngularPartitionLift K δ M i) (2 * Real.pi) :=
  smoothIndicator_periodic K δ (equalAngularCell_periodic M i)

theorem contDiff_equalAngularPartitionLift (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (M : ℕ) (i : Fin M) : ContDiff ℝ ∞ (equalAngularPartitionLift K δ M i) :=
  contDiff_smoothIndicator K hδ (measurableSet_equalAngularCell M i)

end FalconerThetaGauge
