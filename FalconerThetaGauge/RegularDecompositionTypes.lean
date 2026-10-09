/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionMass
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Finset.Image

/-!
# Actual bottom-up types for a finite hierarchical family

Each terminal cell keeps its original weight. A type is formed from the actual mass of
all terminal cells with the same previous type inside the same ancestor. Equal full
types then give exact mass-class agreement for every occupied ancestor fiber.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

variable {α : Type*} [DecidableEq α]

/-- The actual type constructor; `ancestor j` reads height from the terminal cells upward. -/
def regularLeafType (S : Finset α) (weight : α → ℝ) (ancestor : ℕ → α → α)
    (w : ℕ) : ℕ → α → List ℕ
  | 0, x => [regularMassClass w (weight x)]
  | j + 1, x =>
      regularMassClass w (∑ y ∈ S.filter (fun y ↦
        ancestor (j + 1) y = ancestor (j + 1) x ∧
          regularLeafType S weight ancestor w j y = regularLeafType S weight ancestor w j x),
        weight y) :: regularLeafType S weight ancestor w j x

/-- The actual selected ancestor family whose mass supplies the next type entry. -/
def regularNodeFamily (S : Finset α) (weight : α → ℝ) (ancestor : ℕ → α → α)
    (w : ℕ) : ℕ → α → Finset α
  | 0, x => S.filter (fun y ↦ y = x)
  | j + 1, x => S.filter (fun y ↦
      ancestor (j + 1) y = ancestor (j + 1) x ∧
        regularLeafType S weight ancestor w j y = regularLeafType S weight ancestor w j x)

/-- The original weight mass of an actual selected ancestor family. -/
def regularNodeMass (S : Finset α) (weight : α → ℝ) (ancestor : ℕ → α → α)
    (w j : ℕ) (x : α) : ℝ :=
  ∑ y ∈ regularNodeFamily S weight ancestor w j x, weight y

theorem regularLeafType_eq_below (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w : ℕ) {i j : ℕ} (hij : i ≤ j) {x y : α}
    (htype : regularLeafType S weight ancestor w j x =
      regularLeafType S weight ancestor w j y) :
    regularLeafType S weight ancestor w i x = regularLeafType S weight ancestor w i y := by
  induction j with
  | zero => simpa only [Nat.eq_zero_of_le_zero hij] using htype
  | succ j ih =>
    rcases eq_or_lt_of_le hij with hij | hij
    · simpa only [hij] using htype
    · apply ih (Nat.le_of_lt_succ hij)
      exact (List.cons.inj htype).2

theorem regularNodeFamily_eq_of_ancestor_type (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ) {x y : α}
    (hancestor : ancestor (j + 1) x = ancestor (j + 1) y)
    (htype : regularLeafType S weight ancestor w j x =
      regularLeafType S weight ancestor w j y) :
    regularNodeFamily S weight ancestor w (j + 1) x =
      regularNodeFamily S weight ancestor w (j + 1) y := by
  simp only [regularNodeFamily, hancestor, htype]

/-- The construction propagates equal types upward within a common ancestor. -/
theorem regularLeafType_eq_above (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w : ℕ)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    {i j : ℕ} (hij : i ≤ j) {x y : α} (hancestor : ancestor i x = ancestor i y)
    (htype : regularLeafType S weight ancestor w i x =
      regularLeafType S weight ancestor w i y) :
    regularLeafType S weight ancestor w j x = regularLeafType S weight ancestor w j y := by
  induction j with
  | zero => simpa only [Nat.eq_zero_of_le_zero hij] using htype
  | succ j ih =>
    rcases eq_or_lt_of_le hij with hij | hij
    · simpa only [hij] using htype
    · have hprev := ih (Nat.le_of_lt_succ hij)
      have hfamily := regularNodeFamily_eq_of_ancestor_type S weight ancestor w j
        (hnest i (j + 1) (Nat.le_of_lt hij) x y hancestor) hprev
      change regularMassClass w (regularNodeMass S weight ancestor w (j + 1) x) ::
          regularLeafType S weight ancestor w j x =
        regularMassClass w (regularNodeMass S weight ancestor w (j + 1) y) ::
          regularLeafType S weight ancestor w j y
      simp only [regularNodeMass, hfamily, hprev]

theorem regularNodeFamily_subset (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ) (x : α) :
    regularNodeFamily S weight ancestor w j x ⊆ S := by
  cases j <;> exact Finset.filter_subset _ _

theorem mem_regularNodeFamily_self (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ) {x : α} (hx : x ∈ S) :
    x ∈ regularNodeFamily S weight ancestor w j x := by
  cases j <;> simp [regularNodeFamily, hx]

theorem regularNodeMass_bounds (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ)
    (hpositive : ∀ x ∈ S, 0 < weight x) (htotal : (∑ x ∈ S, weight x) ≤ 1)
    {x : α} (hx : x ∈ S) :
    weight x ≤ regularNodeMass S weight ancestor w j x ∧
      regularNodeMass S weight ancestor w j x ≤ 1 := by
  have hsub := regularNodeFamily_subset S weight ancestor w j x
  constructor
  · exact Finset.single_le_sum (fun y hy ↦ (hpositive y (hsub hy)).le)
      (mem_regularNodeFamily_self S weight ancestor w j hx)
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun y hy _ ↦ (hpositive y hy).le)).trans htotal

theorem regularLeafType_eq_of_mem_regularNodeFamily (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ) {x y : α}
    (hy : y ∈ regularNodeFamily S weight ancestor w j x) :
    regularLeafType S weight ancestor w j y = regularLeafType S weight ancestor w j x := by
  cases j with
  | zero =>
    have hxy : y = x := (Finset.mem_filter.mp hy).2
    rw [hxy]
  | succ j =>
    obtain ⟨_, hancestor, hprev⟩ := Finset.mem_filter.mp hy
    have hfamily := regularNodeFamily_eq_of_ancestor_type S weight ancestor w j
      hancestor hprev
    change regularMassClass w (regularNodeMass S weight ancestor w (j + 1) y) ::
        regularLeafType S weight ancestor w j y =
      regularMassClass w (regularNodeMass S weight ancestor w (j + 1) x) ::
        regularLeafType S weight ancestor w j x
    simp only [regularNodeMass, hfamily, hprev]

/-- The precise saturation assertion in the proof of Lemma 5.8: the occupied ancestor
fiber of a final type is exactly the family used to construct its class at that height. -/
theorem regularLeafType_fiber_eq_regularNodeFamily (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w : ℕ) (hzero : ancestor 0 = id)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    {i L : ℕ} (hiL : i ≤ L) (x : α) :
    S.filter (fun y ↦ ancestor i y = ancestor i x ∧
      regularLeafType S weight ancestor w L y = regularLeafType S weight ancestor w L x) =
      regularNodeFamily S weight ancestor w i x := by
  ext y
  cases i with
  | zero =>
    simp [regularNodeFamily, hzero]
    rintro _ rfl
    rfl
  | succ i =>
    simp only [Finset.mem_filter, regularNodeFamily]
    constructor
    · rintro ⟨hy, hancestor, htype⟩
      exact ⟨hy, hancestor,
        regularLeafType_eq_below S weight ancestor w (by omega : i ≤ L) htype⟩
    · rintro ⟨hy, hancestor, hprev⟩
      have htype := regularLeafType_eq_of_mem_regularNodeFamily S weight ancestor w (i + 1)
        (Finset.mem_filter.mpr ⟨hy, hancestor, hprev⟩)
      exact ⟨hy, hancestor,
        regularLeafType_eq_above S weight ancestor w hnest hiL hancestor htype⟩

theorem regularNodeMass_zero (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w : ℕ) {x : α} (hx : x ∈ S) :
    regularNodeMass S weight ancestor w 0 x = weight x := by
  simp [regularNodeMass, regularNodeFamily, Finset.filter_eq', hx]

/-- Equal final types have exactly equal mass classes at every earlier sampled level. -/
theorem regularNodeMass_class_eq_of_type_eq (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w : ℕ) {i L : ℕ} (hiL : i ≤ L) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S)
    (htype : regularLeafType S weight ancestor w L x = regularLeafType S weight ancestor w L y) :
    regularMassClass w (regularNodeMass S weight ancestor w i x) =
      regularMassClass w (regularNodeMass S weight ancestor w i y) := by
  have hbelow := regularLeafType_eq_below S weight ancestor w hiL htype
  cases i with
  | zero =>
    rw [regularNodeMass_zero S weight ancestor w hx,
      regularNodeMass_zero S weight ancestor w hy]
    exact (List.cons.inj hbelow).1
  | succ i => exact (List.cons.inj hbelow).1

/-- Actual ancestor-fiber masses inside one final type are comparable at each sampled level. -/
theorem regularNodeMass_comparable_of_type_eq (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) {w : ℕ} (hw : 0 < w)
    (hpositive : ∀ x ∈ S, 0 < weight x) (htotal : (∑ x ∈ S, weight x) ≤ 1)
    {i L : ℕ} (hiL : i ≤ L) {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (htype : regularLeafType S weight ancestor w L x = regularLeafType S weight ancestor w L y) :
    regularNodeMass S weight ancestor w i x <
      (2 : ℝ) ^ w * regularNodeMass S weight ancestor w i y := by
  have hxmass := regularNodeMass_bounds S weight ancestor w i hpositive htotal hx
  have hymass := regularNodeMass_bounds S weight ancestor w i hpositive htotal hy
  exact regularMassClass_comparable hw ((hpositive x hx).trans_le hxmass.1) hxmass.2
    ((hpositive y hy).trans_le hymass.1) hymass.2
    (regularNodeMass_class_eq_of_type_eq S weight ancestor w hiL hx hy htype)

theorem ancestor_eq_of_mem_regularNodeFamily (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ) {x y : α}
    (hy : y ∈ regularNodeFamily S weight ancestor w j x) :
    ancestor j y = ancestor j x := by
  cases j with
  | zero => rw [(Finset.mem_filter.mp hy).2]
  | succ j => exact (Finset.mem_filter.mp hy).2.1

/-- The constructed selected families really are nested; no terminal weight is changed. -/
theorem regularNodeFamily_subset_succ (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    (x : α) :
    regularNodeFamily S weight ancestor w j x ⊆
      regularNodeFamily S weight ancestor w (j + 1) x := by
  intro y hy
  exact Finset.mem_filter.mpr ⟨regularNodeFamily_subset S weight ancestor w j x hy,
    hnest j (j + 1) (Nat.le_succ j) y x
      (ancestor_eq_of_mem_regularNodeFamily S weight ancestor w j hy),
    regularLeafType_eq_of_mem_regularNodeFamily S weight ancestor w j hy⟩

theorem regularNodeMass_le_succ (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ)
    (hpositive : ∀ x ∈ S, 0 < weight x)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    (x : α) :
    regularNodeMass S weight ancestor w j x ≤ regularNodeMass S weight ancestor w (j + 1) x :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (regularNodeFamily_subset_succ S weight ancestor w j hnest x)
    (fun y hy _ ↦ (hpositive y (regularNodeFamily_subset S weight ancestor w (j + 1) x hy)).le)

/-- Within a selected parent, its child ancestor fiber is the actual selected child family. -/
theorem regularNodeFamily_child_fiber (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) (w j : ℕ) (hzero : ancestor 0 = id)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    {x y : α} (hy : y ∈ regularNodeFamily S weight ancestor w (j + 1) x) :
    (regularNodeFamily S weight ancestor w (j + 1) x).filter
      (fun z ↦ ancestor j z = ancestor j y) = regularNodeFamily S weight ancestor w j y := by
  obtain ⟨hyS, hyancestor, hytype⟩ := Finset.mem_filter.mp hy
  rw [← regularLeafType_fiber_eq_regularNodeFamily S weight ancestor w hzero hnest
    (le_refl j) y]
  ext z
  simp only [regularNodeFamily, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hzS, _, hztype⟩, hzancestor⟩
    exact ⟨hzS, hzancestor, hztype.trans hytype.symm⟩
  · rintro ⟨hzS, hzancestor, hztype⟩
    exact ⟨⟨hzS, (hnest j (j + 1) (Nat.le_succ j) z y hzancestor).trans hyancestor,
      hztype.trans hytype⟩, hzancestor⟩

/-- Counting actual selected children bounds the actual selected-parent mass. -/
theorem regularNodeMass_le_class_upper_mul_child_count (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) {w : ℕ} (hw : 0 < w) (j : ℕ)
    (hpositive : ∀ x ∈ S, 0 < weight x) (htotal : (∑ x ∈ S, weight x) ≤ 1)
    (hzero : ancestor 0 = id)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    {x : α} (hx : x ∈ S) :
    regularNodeMass S weight ancestor w (j + 1) x ≤
      ((regularNodeFamily S weight ancestor w (j + 1) x).image (ancestor j)).card *
        (2 : ℝ) ^ (-((w : ℝ) * regularMassClass w
          (regularNodeMass S weight ancestor w j x))) := by
  let P := regularNodeFamily S weight ancestor w (j + 1) x
  rw [regularNodeMass]
  change (∑ y ∈ P, weight y) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to (fun y hy ↦ Finset.mem_image_of_mem (ancestor j) hy)
    weight]
  calc
    _ ≤ ∑ _q ∈ P.image (ancestor j), (2 : ℝ) ^ (-((w : ℝ) * regularMassClass w
        (regularNodeMass S weight ancestor w j x))) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      rw [regularNodeFamily_child_fiber S weight ancestor w j hzero hnest hy]
      have hyS := regularNodeFamily_subset S weight ancestor w (j + 1) x hy
      have hm := regularNodeMass_bounds S weight ancestor w j hpositive htotal hyS
      have hc := regularNodeMass_class_eq_of_type_eq S weight ancestor w (le_refl j)
        hyS hx (Finset.mem_filter.mp hy).2.2
      have hb := (regularMassClass_bounds hw ((hpositive y hyS).trans_le hm.1) hm.2).2
      rwa [hc] at hb
    _ = _ := by simp [P]

/-- The actual bottom-up construction has no more than nine adjacent class drops whenever
each selected parent has at most `2^(8w)` different selected child ancestors. -/
theorem regularNodeMass_class_step (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) {w : ℕ} (hw : 0 < w) (j : ℕ)
    (hpositive : ∀ x ∈ S, 0 < weight x) (htotal : (∑ x ∈ S, weight x) ≤ 1)
    (hzero : ancestor 0 = id)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    {x : α} (hx : x ∈ S)
    (hcard : ((regularNodeFamily S weight ancestor w (j + 1) x).image (ancestor j)).card ≤
      2 ^ (8 * w)) :
    regularMassClass w (regularNodeMass S weight ancestor w (j + 1) x) ≤
        regularMassClass w (regularNodeMass S weight ancestor w j x) ∧
      regularMassClass w (regularNodeMass S weight ancestor w j x) ≤
        regularMassClass w (regularNodeMass S weight ancestor w (j + 1) x) + 9 := by
  have hm := regularNodeMass_bounds S weight ancestor w j hpositive htotal hx
  have hmnext := regularNodeMass_bounds S weight ancestor w (j + 1) hpositive htotal hx
  apply regularMassClass_parent_gap_le_nine hw ((hpositive x hx).trans_le hm.1) hmnext.2
    (regularNodeMass_le_succ S weight ancestor w j hpositive hnest x)
  have hcount : (((regularNodeFamily S weight ancestor w (j + 1) x).image
      (ancestor j)).card : ℝ) ≤ (2 : ℝ) ^ (8 * w) := by exact_mod_cast hcard
  exact (regularNodeMass_le_class_upper_mul_child_count S weight ancestor hw j
    hpositive htotal hzero hnest hx).trans
      (mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by norm_num) _))

end FalconerThetaGauge
