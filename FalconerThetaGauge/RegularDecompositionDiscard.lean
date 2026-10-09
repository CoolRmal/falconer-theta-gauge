/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionCounting

/-!
# Discarding whole light type classes

The operation retains original cell weights and removes only complete type fibers. Its
loss is bounded by the actual number of types times the specified mass threshold.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The exact mass of one original-weight type fiber. -/
def finiteTypeMass (S : Finset α) (weight : α → ℝ) (type : α → β) (t : β) : ℝ :=
  ∑ x ∈ S.filter (fun x ↦ type x = t), weight x

omit [DecidableEq α] in
/-- Type fibers are disjoint sets of the original terminal cells. -/
theorem finiteTypeFibers_disjoint (S : Finset α) (type : α → β) {t t' : β} (htt' : t ≠ t') :
    Disjoint (S.filter fun x ↦ type x = t) (S.filter fun x ↦ type x = t') := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  exact htt' ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hx').2)

/-- The mass discarded from cells equals the sum of the masses of the discarded whole types. -/
theorem discarded_finiteTypeMass_eq (S : Finset α) (weight : α → ℝ) (type : α → β)
    (threshold : ℝ) :
    (∑ x ∈ S.filter (fun x ↦ finiteTypeMass S weight type (type x) < threshold), weight x) =
      ∑ t ∈ (S.image type).filter (fun t ↦ finiteTypeMass S weight type t < threshold),
        finiteTypeMass S weight type t := by
  calc
    _ = ∑ x ∈ S.filter (fun x ↦ type x ∈
        (S.image type).filter (fun t ↦ finiteTypeMass S weight type t < threshold)), weight x := by
      congr 1
      ext x
      by_cases hx : x ∈ S
      · simp only [Finset.mem_filter, hx, true_and, Finset.mem_image_of_mem type hx]
      · simp [hx]
    _ = _ := (Finset.sum_fiberwise_eq_sum_filter S
      ((S.image type).filter (fun t ↦ finiteTypeMass S weight type t < threshold))
      type weight).symm

/-- The total discarded type mass is bounded by the actual type count times its threshold. -/
theorem discarded_finiteTypeMass_le (S : Finset α) (weight : α → ℝ) (type : α → β)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    (∑ x ∈ S.filter (fun x ↦ finiteTypeMass S weight type (type x) < threshold), weight x) ≤
      (S.image type).card * threshold := by
  rw [discarded_finiteTypeMass_eq]
  exact (discarded_small_weights_sum_le (S.image type) (finiteTypeMass S weight type)
    threshold).trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) hthreshold)

/-- The exact second discard estimate of Lemma 5.8 uses the part threshold tied to `κ`. -/
theorem discard_light_types_le (S : Finset α) (weight : α → ℝ) (type : α → β)
    (κ : ℝ) (N : ℕ) (hcount : ((S.image type).card : ℝ) ≤ (2 : ℝ) ^ (κ * N / 4)) :
    (∑ x ∈ S.filter (fun x ↦ finiteTypeMass S weight type (type x) <
      (2 : ℝ) ^ (-(κ * N / 2))), weight x) ≤ (2 : ℝ) ^ (-(κ * N / 4)) := by
  calc
    _ ≤ _ := discarded_finiteTypeMass_le S weight type (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (κ * N / 4) * (2 : ℝ) ^ (-(κ * N / 2)) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring

end FalconerThetaGauge
