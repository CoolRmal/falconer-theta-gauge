/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionTypes
public import Mathlib.Data.Finset.Prod

/-!
# Counting the actual regular types

The terminal class has a finite range, and every earlier class has at most ten choices
given its child class. Encoding those choices bounds the actual number of final types.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

variable {α : Type*} [DecidableEq α]

theorem regularLeafType_head (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ) {x : α} (hx : x ∈ S) :
    (regularLeafType S weight ancestor w j x).headD 0 =
      regularMassClass w (regularNodeMass S weight ancestor w j x) := by
  cases j with
  | zero => simp [regularLeafType, regularNodeMass_zero S weight ancestor w hx]
  | succ j => rfl

/-- The number of actual types is at most `(M+1)·10^L`: the first entry has `M+1`
choices, and each additional ancestor entry has at most ten choices. -/
theorem card_regularLeafType_image_le (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) {w : ℕ} (hw : 0 < w) (L M : ℕ)
    (hpositive : ∀ x ∈ S, 0 < weight x) (htotal : (∑ x ∈ S, weight x) ≤ 1)
    (hzero : ancestor 0 = id)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    (hterminal : ∀ x ∈ S, regularMassClass w (weight x) ≤ M)
    (hcard : ∀ j < L, ∀ x ∈ S,
      ((regularNodeFamily S weight ancestor w (j + 1) x).image (ancestor j)).card ≤
        2 ^ (8 * w)) :
    (S.image (regularLeafType S weight ancestor w L)).card ≤ (M + 1) * 10 ^ L := by
  induction L with
  | zero =>
    have hsub : S.image (regularLeafType S weight ancestor w 0) ⊆
        (Finset.range (M + 1)).image (fun k ↦ [k]) := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image.mpr ⟨regularMassClass w (weight x),
        Finset.mem_range.mpr (by have := hterminal x hx; omega), rfl⟩
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_image_le).trans (by simp))
  | succ L ih =>
    have ih := ih (fun j hj x hx ↦ hcard j (by omega) x hx)
    let E := (S.image (regularLeafType S weight ancestor w L)).product (Finset.range 10)
    let decode : List ℕ × ℕ → List ℕ := fun p ↦ (p.1.headD 0 - p.2) :: p.1
    have hsub : S.image (regularLeafType S weight ancestor w (L + 1)) ⊆ E.image decode := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      let c := regularMassClass w (regularNodeMass S weight ancestor w L x)
      let c' := regularMassClass w (regularNodeMass S weight ancestor w (L + 1) x)
      have hstep := regularNodeMass_class_step S weight ancestor hw L hpositive htotal
        hzero hnest hx (hcard L (Nat.lt_succ_self L) x hx)
      change c' ≤ c ∧ c ≤ c' + 9 at hstep
      refine Finset.mem_image.mpr ⟨(regularLeafType S weight ancestor w L x, c - c'), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
          Finset.mem_range.mpr (by omega)⟩
      · change ((regularLeafType S weight ancestor w L x).headD 0 - (c - c')) ::
          regularLeafType S weight ancestor w L x = _
        rw [regularLeafType_head S weight ancestor w L hx]
        have hc : c - (c - c') = c' := by omega
        rw [hc]
        rfl
    calc
      _ ≤ (E.image decode).card := Finset.card_le_card hsub
      _ ≤ E.card := Finset.card_image_le
      _ = (S.image (regularLeafType S weight ancestor w L)).card * 10 := by
        simp [E]
      _ ≤ ((M + 1) * 10 ^ L) * 10 := Nat.mul_le_mul_right 10 ih
      _ = _ := by rw [pow_succ, Nat.mul_assoc]

end FalconerThetaGauge
