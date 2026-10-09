/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainStates

/-!
# Marked-depth progress of the actual moves

The near-child alternative is proved using the actual remaining tests: a
long near child either passes an anchor of a longest test, or keeps a longest
test and forces its next move to be refinement.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

theorem ProfileChainMove.tag_le_five {A : ℕ → ℝ} {q N δ : ℕ}
    {s u : ProfileChainState} (move : ProfileChainMove A q N δ s u) : move.tag ≤ 5 := by
  cases move <;> simp [ProfileChainMove.tag]

/-- The two moves to a marked depth strictly increase the start. -/
theorem ProfileChainMove.marked_start {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) {s u : ProfileChainState} (hs : s.Valid N δ)
    (move : ProfileChainMove A q N δ s u) (htag : move.tag = 2 ∨ move.tag = 3) :
    s.start < u.start ∧ u.start ∈ profileMarkedDepths A q N := by
  cases move with
  | highFrequency a t v hlong hleft hvlo hvhi =>
    obtain ⟨_, ht⟩ := hs
    have hp := profileSplitPoint_bounds (A := A) hq ht hlong
    exact ⟨by change a < profileSplitPoint A q N a t; omega,
      profileSplitPoint_mem_marked hq ht hlong⟩
  | refine b e a v hlong test htest hlargest hlarge =>
    obtain ⟨_, _, _, he, _⟩ := hs
    obtain ⟨hlist, hanchor⟩ := Finset.mem_filter.mp htest
    exact ⟨hanchor, profileScheduledTests_anchor_mem hq he hlist⟩
  | _ => simp [ProfileChainMove.tag] at htag

/-- A linearization step lowers the end by at least one complete depth block. -/
theorem ProfileChainMove.linearize_end_drop {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) {s u : ProfileChainState} (hs : s.Valid N δ)
    (move : ProfileChainMove A q N δ s u) (htag : move.tag = 0) :
    q ≤ s.finish - u.finish := by
  cases move with
  | linearize a t hlong hright =>
    obtain ⟨_, ht⟩ := hs
    have hp := profileSplitPoint_bounds (A := A) hq ht hlong
    change q ≤ t - profileSplitPoint A q N a t
    omega
  | _ => simp [ProfileChainMove.tag] at htag

/-- The low-frequency child lowers the end by exactly its shell thickness. -/
theorem ProfileChainMove.lowFrequency_end_drop {A : ℕ → ℝ} {q N δ : ℕ}
    (hδq : δ ≤ q) {s u : ProfileChainState} (hs : s.Valid N δ)
    (move : ProfileChainMove A q N δ s u) (htag : move.tag = 1) :
    δ ≤ s.finish - u.finish := by
  cases move with
  | lowFrequency a t hlong hleft =>
    obtain ⟨hat, _⟩ := hs
    change δ ≤ t - (t - δ)
    omega
  | _ => simp [ProfileChainMove.tag] at htag

/-- A long near child either passes a longest-test anchor or keeps a longest test
whose length is precisely half the child's interval length. -/
theorem profileNearStep_longest_dichotomy {A : ℕ → ℝ} {q N δ b e a v : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) (hav : a ≤ v)
    (hsmall : 2 * profileLongestTestLength A q N b e a < v - a)
    (hchild : 100 * q < v - (v - 2 * max (profileLongestTestLength A q N b e a) δ)) :
    ∃ test ∈ profileRemainingTests A q N b e a,
      test.length = profileLongestTestLength A q N b e a ∧
      (test.anchor ≤ v - 2 * max (profileLongestTestLength A q N b e a) δ ∨
        (profileLongestTestLength A q N b e
          (v - 2 * max (profileLongestTestLength A q N b e a) δ) = test.length ∧
          v - (v - 2 * max (profileLongestTestLength A q N b e a) δ) =
            2 * test.length)) := by
  let L := profileLongestTestLength A q N b e a
  have hδL : δ ≤ L := by
    change 100 * q < v - (v - 2 * max L δ) at hchild
    omega
  have hmax : max L δ = L := max_eq_left hδL
  have hLpos : 0 < L := by
    change 100 * q < v - (v - 2 * max L δ) at hchild
    rw [hmax] at hchild
    omega
  obtain ⟨test, htest, hlen⟩ := profileLongestTestLength_attained hLpos
  refine ⟨test, htest, hlen, ?_⟩
  by_cases hpassed : test.anchor ≤ v - 2 * max L δ
  · exact Or.inl hpassed
  · right
    have hretained : test ∈ profileRemainingTests A q N b e (v - 2 * max L δ) := by
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp htest).1, by omega⟩
    have hlow := Finset.le_sup (f := ProfileScheduleTest.length) hretained
    have hhigh := profileLongestTestLength_mono A q N b e (a := a)
      (c := v - 2 * max L δ) (by change 2 * L < v - a at hsmall; rw [hmax]; omega)
    refine ⟨le_antisymm (hhigh.trans_eq hlen.symm) hlow, ?_⟩
    change v - (v - 2 * max L δ) = 2 * test.length
    change test.length = L at hlen
    change 2 * L < v - a at hsmall
    rw [hmax, hlen]
    omega

/-- If a near child has a next move, it either crosses a marked depth or that
next move is the refinement of a longest test. -/
theorem ProfileChainMove.near_next {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) {s u w : ProfileChainState} (hs : s.Valid N δ)
    (move : ProfileChainMove A q N δ s u) (htag : move.tag = 4)
    (next : ProfileChainMove A q N δ u w) :
    (∃ p ∈ profileMarkedDepths A q N, s.start < p ∧ p ≤ u.start) ∨ next.tag = 3 := by
  cases move with
  | near b e a v hlong hsmall =>
    obtain ⟨_, hav, _, he, _⟩ := hs
    obtain ⟨test, htest, hlen, hcase⟩ :=
      profileNearStep_longest_dichotomy hq hδq hav hsmall next.long
    rcases hcase with hpassed | ⟨hnew, hhalf⟩
    · left
      obtain ⟨hlist, hanchor⟩ := Finset.mem_filter.mp htest
      exact ⟨test.anchor, profileScheduledTests_anchor_mem hq he hlist, hanchor, hpassed⟩
    · right
      cases next with
      | refine b' e' a' v' hlong' test' htest' hlargest' hlarge' => rfl
      | near b' e' a' v' hlong' hsmall' => omega
      | far b' e' a' v' n hlong' hsmall' hnlo hnhi hnv => omega
  | _ => simp [ProfileChainMove.tag] at htag

end FalconerThetaGauge
