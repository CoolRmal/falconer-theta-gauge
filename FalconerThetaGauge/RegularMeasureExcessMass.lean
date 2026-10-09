/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionCells
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Actual largest dyadic cell masses

The largest cell mass of a probability carried by the unit square is attained,
positive, equal to one at generation zero, and changes by a factor between one
and four at each dyadic refinement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem unitCellIndices_nonempty (n : ℕ) : (unitCellIndices n).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_unitCellIndices]
  positivity

/-- The actual largest mass among the generation-`n` cells of the unit square. -/
def maxCellMass (μ : Measure Plane) (n : ℕ) : ℝ :=
  (unitCellIndices n).sup' (unitCellIndices_nonempty n) (unitCellWeight μ n)

theorem unitCellWeight_le_maxCellMass (μ : Measure Plane) (n : ℕ) {k : Fin 2 → ℤ}
    (hk : k ∈ unitCellIndices n) : unitCellWeight μ n k ≤ maxCellMass μ n :=
  Finset.le_sup' _ hk

theorem exists_unitCellWeight_eq_maxCellMass (μ : Measure Plane) (n : ℕ) :
    ∃ k ∈ unitCellIndices n, maxCellMass μ n = unitCellWeight μ n k :=
  Finset.exists_mem_eq_sup' (unitCellIndices_nonempty n) _

theorem maxCellMass_nonneg (μ : Measure Plane) (n : ℕ) : 0 ≤ maxCellMass μ n := by
  obtain ⟨k, hk, hmass⟩ := exists_unitCellWeight_eq_maxCellMass μ n
  rw [hmass]
  exact unitCellWeight_nonneg μ n k

theorem maxCellMass_le_one (μ : Measure Plane) [IsProbabilityMeasure μ] (n : ℕ) :
    maxCellMass μ n ≤ 1 := by
  obtain ⟨k, _, hmass⟩ := exists_unitCellWeight_eq_maxCellMass μ n
  rw [hmass]
  simp [unitCellWeight]

theorem maxCellMass_pos (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) (n : ℕ) : 0 < maxCellMass μ n := by
  rw [maxCellMass, Finset.lt_sup'_iff]
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hsum := Finset.sum_nonpos (fun k hk ↦ h k hk)
  rw [sum_unitCellWeight_eq_one μ n hμ] at hsum
  linarith

theorem maxCellMass_zero (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) : maxCellMass μ 0 = 1 := by
  have hcard : (unitCellIndices 0).card = 1 := by rw [card_unitCellIndices]; norm_num
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have hsum := sum_unitCellWeight_eq_one μ 0 hμ
  rw [hk, Finset.sum_singleton] at hsum
  simp only [maxCellMass, hk, Finset.sup'_singleton]
  exact hsum

/-- A child index inside the unit square has its parent index inside the unit square. -/
theorem ancestor_one_mem_unitCellIndices (n : ℕ) {k : Fin 2 → ℤ}
    (hk : k ∈ unitCellIndices (n + 1)) : ancestor 1 k ∈ unitCellIndices n := by
  apply (mem_unitCellIndices_iff n _).mpr
  intro i
  have hi := (mem_unitCellIndices_iff (n + 1) k).mp hk i
  change 0 ≤ k i / 2 ∧ k i / 2 < (2 : ℤ) ^ n
  rw [pow_succ] at hi
  omega

theorem maxCellMass_succ_le (μ : Measure Plane) [IsFiniteMeasure μ] (n : ℕ) :
    maxCellMass μ (n + 1) ≤ maxCellMass μ n := by
  obtain ⟨k, hk, hmass⟩ := exists_unitCellWeight_eq_maxCellMass μ (n + 1)
  rw [hmass]
  exact (measureReal_mono (dyadicCube_subset_ancestor n 1 k)).trans
    (unitCellWeight_le_maxCellMass μ n (ancestor_one_mem_unitCellIndices n hk))

/-- A parent mass is exactly the sum of its actual unit-square child masses. -/
theorem unitCellWeight_eq_sum_children (μ : Measure Plane) [IsFiniteMeasure μ] (n : ℕ)
    {p : Fin 2 → ℤ} (hp : p ∈ unitCellIndices n) :
    unitCellWeight μ n p =
      ∑ k ∈ (unitCellIndices (n + 1)).filter (fun k ↦ ancestor 1 k = p),
        unitCellWeight μ (n + 1) k := by
  have hsum := real_restrict_cellUnion_dyadicCube μ (show n ≤ n + 1 by omega)
    (unitCellIndices (n + 1)) p
  have hcarrier : cellUnion (n + 1) (unitCellIndices (n + 1)) = unitSquare :=
    biUnion_unitCellIndices (n + 1)
  rw [hcarrier, Measure.real, Measure.restrict_apply (measurableSet_dyadicCube n p),
    Set.inter_eq_left.mpr (dyadicCube_subset_unitSquare n hp)] at hsum
  simpa only [unitCellWeight, Measure.real, Nat.add_sub_cancel_left] using hsum

theorem maxCellMass_le_four_mul_succ (μ : Measure Plane) [IsFiniteMeasure μ] (n : ℕ) :
    maxCellMass μ n ≤ 4 * maxCellMass μ (n + 1) := by
  obtain ⟨p, hp, hmass⟩ := exists_unitCellWeight_eq_maxCellMass μ n
  let C := (unitCellIndices (n + 1)).filter (fun k ↦ ancestor 1 k = p)
  have hcard : C.card ≤ 4 := by
    have h := card_image_ancestor_le C 0 1 p
      (fun k hk ↦ (Finset.mem_filter.mp hk).2)
    have hzero : ancestor 0 = id := by funext k; exact ancestor_zero k
    simpa only [Nat.zero_add, hzero, Finset.image_id, pow_one] using h
  rw [hmass, unitCellWeight_eq_sum_children μ n hp]
  calc
    _ ≤ ∑ _k ∈ C, maxCellMass μ (n + 1) :=
      Finset.sum_le_sum (fun k hk ↦ unitCellWeight_le_maxCellMass μ (n + 1)
        (Finset.mem_filter.mp hk).1)
    _ = (C.card : ℝ) * maxCellMass μ (n + 1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (maxCellMass_nonneg μ (n + 1))

end FalconerThetaGauge
