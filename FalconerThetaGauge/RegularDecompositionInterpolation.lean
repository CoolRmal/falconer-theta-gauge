/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionDiscard

/-!
# Regularity between sampled depths

Every intermediate ancestor fiber contains an occupied sampled child fiber and lies
inside its sampled parent fiber. Counting the actual parent children gives the precise
mass-comparability estimate on every intervening partition.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

variable {α β : Type*} [DecidableEq α]

/-- The actual fiber of an intermediate partition inside one final regular type. -/
def regularIntermediateFamily (S : Finset α) (weight : α → ℝ) (ancestor : ℕ → α → α)
    (w L : ℕ) (partition : α → β) (x : α) : Finset α :=
  S.filter (fun y ↦ partition y = partition x ∧
    regularLeafType S weight ancestor w L y = regularLeafType S weight ancestor w L x)

theorem regularNodeFamily_subset_intermediate (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w : ℕ)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    {j L : ℕ} (hjL : j ≤ L) (partition : α → β)
    (hfine : ∀ x y, ancestor j x = ancestor j y → partition x = partition y) (x : α) :
    regularNodeFamily S weight ancestor w j x ⊆
      regularIntermediateFamily S weight ancestor w L partition x := by
  intro y hy
  have hancestor := ancestor_eq_of_mem_regularNodeFamily S weight ancestor w j hy
  exact Finset.mem_filter.mpr ⟨regularNodeFamily_subset S weight ancestor w j x hy,
    hfine y x hancestor,
    regularLeafType_eq_above S weight ancestor w hnest hjL hancestor
      (regularLeafType_eq_of_mem_regularNodeFamily S weight ancestor w j hy)⟩

theorem regularIntermediateFamily_subset_parent (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w : ℕ) {j L : ℕ} (hjL : j ≤ L) (partition : α → β)
    (hcoarse : ∀ x y, partition x = partition y →
      ancestor (j + 1) x = ancestor (j + 1) y) (x : α) :
    regularIntermediateFamily S weight ancestor w L partition x ⊆
      regularNodeFamily S weight ancestor w (j + 1) x := by
  intro y hy
  obtain ⟨hyS, hypartition, hytype⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hyS, hcoarse y x hypartition,
    regularLeafType_eq_below S weight ancestor w hjL hytype⟩

/-- Actual intermediate fibers of one final type are comparable by `2^(D+w)` when
there are at most `2^D` sampled children in each sampled parent. -/
theorem regularIntermediateFamily_mass_comparable (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) {w : ℕ} (hw : 0 < w)
    (hpositive : ∀ x ∈ S, 0 < weight x) (htotal : (∑ x ∈ S, weight x) ≤ 1)
    (hzero : ancestor 0 = id)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    {j L : ℕ} (hjL : j ≤ L) (partition : α → β)
    (hfine : ∀ x y, ancestor j x = ancestor j y → partition x = partition y)
    (hcoarse : ∀ x y, partition x = partition y →
      ancestor (j + 1) x = ancestor (j + 1) y)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (htype : regularLeafType S weight ancestor w L x = regularLeafType S weight ancestor w L y)
    (D : ℕ)
    (hcard : ((regularNodeFamily S weight ancestor w (j + 1) x).image (ancestor j)).card ≤
      2 ^ D) :
    (∑ z ∈ regularIntermediateFamily S weight ancestor w L partition x, weight z) <
      (2 : ℝ) ^ (D + w) *
        ∑ z ∈ regularIntermediateFamily S weight ancestor w L partition y, weight z := by
  have hupper : (∑ z ∈ regularIntermediateFamily S weight ancestor w L partition x,
      weight z) ≤ regularNodeMass S weight ancestor w (j + 1) x :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (regularIntermediateFamily_subset_parent S weight ancestor w hjL partition hcoarse x)
      (fun z hz _ ↦ (hpositive z
        (regularNodeFamily_subset S weight ancestor w (j + 1) x hz)).le)
  have hlower : regularNodeMass S weight ancestor w j y ≤
      ∑ z ∈ regularIntermediateFamily S weight ancestor w L partition y, weight z :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (regularNodeFamily_subset_intermediate S weight ancestor w hnest hjL partition hfine y)
      (fun z hz _ ↦ (hpositive z (Finset.mem_filter.mp hz).1).le)
  have hymass := regularNodeMass_bounds S weight ancestor w j hpositive htotal hy
  have hchildlower := (regularMassClass_bounds hw ((hpositive y hy).trans_le hymass.1)
    hymass.2).1
  have hclass := regularNodeMass_class_eq_of_type_eq S weight ancestor w hjL hx hy htype
  rw [← hclass] at hchildlower
  have hcount : (((regularNodeFamily S weight ancestor w (j + 1) x).image
      (ancestor j)).card : ℝ) ≤ (2 : ℝ) ^ D := by exact_mod_cast hcard
  have hparentupper := (regularNodeMass_le_class_upper_mul_child_count S weight ancestor hw j
    hpositive htotal hzero hnest hx).trans
      (mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by norm_num) _))
  have heq : (2 : ℝ) ^ (D + w) *
      (2 : ℝ) ^ (-((w : ℝ) * (regularMassClass w
        (regularNodeMass S weight ancestor w j x) + 1))) =
      (2 : ℝ) ^ D * (2 : ℝ) ^ (-((w : ℝ) * regularMassClass w
        (regularNodeMass S weight ancestor w j x))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (2 : ℝ) ^ D * (2 : ℝ) ^ (-((w : ℝ) * regularMassClass w
        (regularNodeMass S weight ancestor w j x))) := hupper.trans hparentupper
    _ < (2 : ℝ) ^ (D + w) * regularNodeMass S weight ancestor w j y := by
      rw [← heq]
      exact mul_lt_mul_of_pos_left hchildlower (pow_pos (by norm_num) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (pow_nonneg (by norm_num) _)

end FalconerThetaGauge
