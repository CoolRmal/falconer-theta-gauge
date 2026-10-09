/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith

/-!
# Exact mass buckets and discard bounds for regular decomposition

These are the quantitative finite-mass ingredients of Lemma 5.8. The bucket is the actual
floor of the logarithmic mass, and the discard operation removes whole original cells.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The mass class of Lemma 5.8, with logarithm base two and bucket width `w`. -/
def regularMassClass (w : ℕ) (m : ℝ) : ℕ :=
  ⌊-Real.log m / ((w : ℝ) * Real.log 2)⌋₊

/-- The actual floor bucket gives the exact strict lower and closed upper mass bounds. -/
theorem regularMassClass_bounds {w : ℕ} (hw : 0 < w) {m : ℝ}
    (hm : 0 < m) (hm₁ : m ≤ 1) :
    (2 : ℝ) ^ (-((w : ℝ) * (regularMassClass w m + 1))) < m ∧
      m ≤ (2 : ℝ) ^ (-((w : ℝ) * regularMassClass w m)) := by
  have hw' : (0 : ℝ) < w := Nat.cast_pos.mpr hw
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < (w : ℝ) * Real.log 2 := mul_pos hw' hlog
  have hratio : 0 ≤ -Real.log m / ((w : ℝ) * Real.log 2) :=
    div_nonneg (neg_nonneg.mpr (Real.log_nonpos hm.le hm₁)) hd.le
  have hlo := (le_div_iff₀ hd).mp (Nat.floor_le hratio)
  have hhi := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one
    (-Real.log m / ((w : ℝ) * Real.log 2)))
  change (regularMassClass w m : ℝ) * ((w : ℝ) * Real.log 2) ≤ -Real.log m at hlo
  change -Real.log m < (regularMassClass w m + 1) * ((w : ℝ) * Real.log 2) at hhi
  constructor
  · rw [Real.rpow_def_of_pos (by norm_num)]
    have he : Real.log 2 * -((w : ℝ) * (regularMassClass w m + 1)) < Real.log m := by
      nlinarith
    exact (Real.exp_lt_exp.mpr he).trans_eq (Real.exp_log hm)
  · rw [Real.rpow_def_of_pos (by norm_num)]
    have he : Real.log m ≤ Real.log 2 * -((w : ℝ) * regularMassClass w m) := by
      nlinarith
    simpa only [Real.exp_log hm] using Real.exp_le_exp.mpr he

/-- Mass classification reverses the order of positive masses. -/
theorem regularMassClass_antitone {w : ℕ} {m m' : ℝ}
    (hm : 0 < m) (hmm' : m ≤ m') :
    regularMassClass w m' ≤ regularMassClass w m := by
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_right
    (neg_le_neg (Real.log_le_log hm hmm'))
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))

/-- Members of the same actual bucket have masses within the specified factor `2^w`. -/
theorem regularMassClass_comparable {w : ℕ} (hw : 0 < w) {m m' : ℝ}
    (hm : 0 < m) (hm₁ : m ≤ 1) (hm' : 0 < m') (hm'₁ : m' ≤ 1)
    (hclass : regularMassClass w m = regularMassClass w m') :
    m < (2 : ℝ) ^ w * m' := by
  have h₁ := (regularMassClass_bounds hw hm hm₁).2
  have h₂ := (regularMassClass_bounds hw hm' hm'₁).1
  rw [← hclass] at h₂
  have heq : (2 : ℝ) ^ w * (2 : ℝ) ^ (-((w : ℝ) *
      (regularMassClass w m + 1))) = (2 : ℝ) ^ (-((w : ℝ) * regularMassClass w m)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hmul := mul_lt_mul_of_pos_left h₂ (pow_pos (by norm_num : (0 : ℝ) < 2) w)
  rw [heq] at hmul
  exact h₁.trans_lt hmul

/-- Any union of heavy terminal cells belongs to the finite range of mass classes. -/
theorem regularMassClass_le_of_heavy {w N : ℕ} (hw : 0 < w) {m : ℝ}
    (hheavy : (2 : ℝ) ^ (-(3 * (N : ℝ))) ≤ m) :
    regularMassClass w m ≤ ⌊3 * (N : ℝ) / w⌋₊ := by
  apply Nat.floor_le_floor
  have hd : 0 < (w : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hw) (Real.log_pos (by norm_num))
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) hheavy
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  apply (div_le_iff₀ hd).mpr
  have hw' : (w : ℝ) ≠ 0 := (Nat.cast_pos.mpr hw).ne'
  field_simp
  nlinarith

/-- Removing all weights below a threshold costs at most the cell count times the threshold. -/
theorem discarded_small_weights_sum_le {α : Type*} (S : Finset α) (weight : α → ℝ)
    (threshold : ℝ) :
    (∑ x ∈ S.filter (fun x ↦ weight x < threshold), weight x) ≤
      (S.filter (fun x ↦ weight x < threshold)).card * threshold := by
  calc
    _ ≤ ∑ _x ∈ S.filter (fun x ↦ weight x < threshold), threshold :=
      Finset.sum_le_sum fun _ hx ↦ (Finset.mem_filter.mp hx).2.le
    _ = _ := by simp

/-- The exact Step 0 bound: among at most `4^N` terminal cells, deleting masses below
`2^(-3N)` loses at most `2^(-N)`. -/
theorem discard_light_terminal_cells_le {α : Type*} (S : Finset α) (weight : α → ℝ)
    (N : ℕ) (hcard : S.card ≤ 4 ^ N) :
    (∑ x ∈ S.filter (fun x ↦ weight x < (2 : ℝ) ^ (-(3 * (N : ℝ)))), weight x) ≤
      (2 : ℝ) ^ (-(N : ℝ)) := by
  have hcount : ((S.filter fun x ↦ weight x < (2 : ℝ) ^ (-(3 * (N : ℝ)))).card : ℝ) ≤
      (4 : ℝ) ^ N := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  calc
    _ ≤ _ := discarded_small_weights_sum_le S weight _
    _ ≤ (4 : ℝ) ^ N * (2 : ℝ) ^ (-(3 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [show (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * (N : ℝ)) by
        rw [Real.rpow_mul (by norm_num)]
        norm_num]
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring

/-- The sharp adjacent-class estimate used in counting types: a parent made from at most
`2^(8w)` children of one class has no more than nine downward class steps. -/
theorem regularMassClass_parent_gap_le_nine {w : ℕ} (hw : 0 < w) {child parent : ℝ}
    (hchild : 0 < child) (hparent₁ : parent ≤ 1)
    (hchildparent : child ≤ parent)
    (hparent : parent ≤ (2 : ℝ) ^ (8 * w) *
      (2 : ℝ) ^ (-((w : ℝ) * regularMassClass w child))) :
    regularMassClass w parent ≤ regularMassClass w child ∧
      regularMassClass w child ≤ regularMassClass w parent + 9 := by
  refine ⟨regularMassClass_antitone hchild hchildparent, ?_⟩
  have hlow := (regularMassClass_bounds hw (hchild.trans_le hchildparent) hparent₁).1
  have hpow : (2 : ℝ) ^ (-((w : ℝ) * (regularMassClass w parent + 1))) <
      (2 : ℝ) ^ (8 * (w : ℝ) - (w : ℝ) * regularMassClass w child) := by
    convert hlow.trans_le hparent using 1
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  have hexp := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow
  have hw' : (0 : ℝ) < w := Nat.cast_pos.mpr hw
  have hclass : (regularMassClass w child : ℝ) < regularMassClass w parent + 9 := by
    nlinarith
  have hnat : regularMassClass w child < regularMassClass w parent + 9 := by
    exact_mod_cast hclass
  exact hnat.le

end FalconerThetaGauge
