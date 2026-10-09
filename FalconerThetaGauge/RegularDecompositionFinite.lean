/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionParameters

/-!
# Quantitative regular decomposition of original finite cell weights

The heavy terminal cells are typed using their original masses, and only whole light
types are discarded. The two exact discard estimates combine with the stated (P2)
budget at the terminal scale.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Step 0 retains exactly the terminal cells of mass at least `2^(-3N)`. -/
def heavyTerminalCells (S : Finset α) (weight : α → ℝ) (N : ℕ) : Finset α :=
  S.filter (fun x ↦ (2 : ℝ) ^ (-(3 * (N : ℝ))) ≤ weight x)

/-- The final operation retains whole type fibers whose original mass reaches `2^(-κN/2)`. -/
def retainedRegularLeaves (S : Finset α) (weight : α → ℝ) (type : α → β)
    (κ : ℝ) (N : ℕ) : Finset α :=
  S.filter (fun x ↦ (2 : ℝ) ^ (-(κ * N / 2)) ≤ finiteTypeMass S weight type (type x))

omit [DecidableEq α] [DecidableEq β] in
theorem heavyTerminalCells_positive (S : Finset α) (weight : α → ℝ) (N : ℕ) :
    ∀ x ∈ heavyTerminalCells S weight N, 0 < weight x := by
  intro x hx
  exact (Real.rpow_pos_of_pos (by norm_num) _).trans_le (Finset.mem_filter.mp hx).2

omit [DecidableEq β] in
/-- The actual heavy-cell types fit the exact (P2) count budget. -/
theorem heavyTerminalCells_type_count_le (S : Finset α) (weight : α → ℝ)
    (ancestor : ℕ → α → α) {ε κ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (N : ℕ)
    (hεN : 16 ≤ ε * N) (hweight : ∀ x ∈ S, 0 ≤ weight x)
    (htotal : (∑ x ∈ S, weight x) ≤ 1) (hzero : ancestor 0 = id)
    (hnest : ∀ i j, i ≤ j → ∀ x y, ancestor i x = ancestor i y → ancestor j x = ancestor j y)
    (hbranch : ∀ j < regularDecompositionBlockCount ε N,
      ∀ x ∈ heavyTerminalCells S weight N,
        ((regularNodeFamily (heavyTerminalCells S weight N) weight ancestor
          (regularDecompositionBucketWidth ε N) (j + 1) x).image (ancestor j)).card ≤
            4 ^ regularDecompositionBlockLength ε N)
    (hbudget : Real.log (49 / ε) / Real.log 2 + (333 / 100 : ℝ) * (8 / ε + 1) ≤ κ * N / 4) :
    (((heavyTerminalCells S weight N).image (regularLeafType (heavyTerminalCells S weight N)
      weight ancestor (regularDecompositionBucketWidth ε N)
        (regularDecompositionBlockCount ε N))).card : ℝ) ≤ (2 : ℝ) ^ (κ * N / 4) := by
  let H := heavyTerminalCells S weight N
  let w := regularDecompositionBucketWidth ε N
  let L := regularDecompositionBlockCount ε N
  let M := ⌊3 * (N : ℝ) / w⌋₊
  have hw : 0 < w := regularDecomposition_bucketWidth_pos hεN
  have htotalH : (∑ x ∈ H, weight x) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x hx _ ↦ hweight x hx)).trans htotal
  have hcount := card_regularLeafType_image_le H weight ancestor hw L M
    (heavyTerminalCells_positive S weight N) htotalH hzero hnest
    (fun x hx ↦ regularMassClass_le_of_heavy hw (Finset.mem_filter.mp hx).2)
    (fun j hj x hx ↦ (hbranch j hj x hx).trans (regularDecomposition_childCount_le hεN))
  have hcount' : ((H.image (regularLeafType H weight ancestor w L)).card : ℝ) ≤
      ((M + 1) * 10 ^ L : ℕ) := by exact_mod_cast hcount
  exact hcount'.trans (regularDecomposition_typeCount_budget hε hε₁ hεN hbudget)

omit [DecidableEq α] in
/-- Retaining leaves retains complete original type fibers, including their original mass. -/
theorem retainedRegularLeaves_fiber (S : Finset α) (weight : α → ℝ) (type : α → β)
    (κ : ℝ) (N : ℕ) (t : β) :
    (retainedRegularLeaves S weight type κ N).filter (fun x ↦ type x = t) =
      if (2 : ℝ) ^ (-(κ * N / 2)) ≤ finiteTypeMass S weight type t then
        S.filter (fun x ↦ type x = t) else ∅ := by
  ext x
  by_cases ht : (2 : ℝ) ^ (-(κ * N / 2)) ≤ finiteTypeMass S weight type t
  · simp only [retainedRegularLeaves, Finset.mem_filter, ht, ite_true]
    constructor
    · rintro ⟨⟨hx, _⟩, hxt⟩
      exact ⟨hx, hxt⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hx, hxt ▸ ht⟩, hxt⟩
  · simp only [retainedRegularLeaves, Finset.mem_filter, ht, ite_false, Finset.notMem_empty,
      iff_false]
    rintro ⟨⟨_, hxmass⟩, hxt⟩
    exact ht (hxt ▸ hxmass)

/-- The original terminal weights discarded in both steps satisfy the literal error
`2 R^(-κ/4)`, with the retained-part threshold `R^(-κ/2)`. -/
theorem regularDecomposition_discarded_mass_le (S : Finset α) (weight : α → ℝ)
    (type : α → β) (κ : ℝ) (N : ℕ) (hκ : κ ≤ 4) (hcard : S.card ≤ 4 ^ N)
    (hcount : (((heavyTerminalCells S weight N).image type).card : ℝ) ≤
      (2 : ℝ) ^ (κ * N / 4)) :
    (∑ x ∈ S \ retainedRegularLeaves (heavyTerminalCells S weight N) weight type κ N,
      weight x) ≤ 2 * (2 : ℝ) ^ (-(κ * N / 4)) := by
  let H := heavyTerminalCells S weight N
  let K := retainedRegularLeaves H weight type κ N
  have hKH : K ⊆ H := Finset.filter_subset _ _
  have hHS : H ⊆ S := Finset.filter_subset _ _
  have hsplit : (∑ x ∈ S \ K, weight x) =
      (∑ x ∈ S \ H, weight x) + ∑ x ∈ H \ K, weight x := by
    have h₁ := Finset.sum_sdiff (f := weight) hKH
    have h₂ := Finset.sum_sdiff (f := weight) hHS
    have h₃ := Finset.sum_sdiff (f := weight) (hKH.trans hHS)
    linarith
  have hfirst : (∑ x ∈ S \ H, weight x) ≤ (2 : ℝ) ^ (-(N : ℝ)) := by
    have heq : S \ H = S.filter (fun x ↦ weight x < (2 : ℝ) ^ (-(3 * (N : ℝ)))) := by
      ext x
      simp [H, heavyTerminalCells]
      intro hx
      exact Or.inl hx
    rw [heq]
    exact discard_light_terminal_cells_le S weight N hcard
  have hsecond : (∑ x ∈ H \ K, weight x) ≤ (2 : ℝ) ^ (-(κ * N / 4)) := by
    have heq : H \ K = H.filter (fun x ↦ finiteTypeMass H weight type (type x) <
        (2 : ℝ) ^ (-(κ * N / 2))) := by
      ext x
      simp [K, retainedRegularLeaves]
      intro hx
      exact Or.inl hx
    rw [heq]
    exact discard_light_types_le H weight type κ N hcount
  have hpower : (2 : ℝ) ^ (-(N : ℝ)) ≤ (2 : ℝ) ^ (-(κ * N / 4)) := by
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [hsplit]
  linarith

end FalconerThetaGauge
