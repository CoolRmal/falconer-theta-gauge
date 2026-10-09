/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainShort

/-!
# Actual budget costs of the induction moves

Linearization and high-frequency children have their exact interval-height
costs. Refinement uses the manuscript's permitted upper cost on `[a,p]`.
The genuine origin of its longest test proves that this cost is paid.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The exact height cost, or the allowed refinement upper cost, in Table 1. -/
def ProfileChainMove.budgetCost {A : ℕ → ℝ} {q N δ : ℕ} {s u : ProfileChainState} :
    ProfileChainMove A q N δ s u → ℝ
  | .linearize a t _ _ =>
      profileHeight A (profileSplitPoint A q N a t) (profileSplitPoint A q N a t) t
  | .lowFrequency .. => 0
  | .highFrequency a t _ _ _ _ _ =>
      profileHeight A (profileSplitPoint A q N a t) a (profileSplitPoint A q N a t)
  | .refine _ _ a _ _ test _ _ _ => profileHeight A test.anchor a test.anchor
  | .near .. => 0
  | .far .. => 0

theorem ProfileChainMove.budgetCost_nonneg {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) {s u : ProfileChainState} (hs : s.Valid N δ)
    (move : ProfileChainMove A q N δ s u) : 0 ≤ move.budgetCost := by
  cases move with
  | linearize a t hlong hright =>
    have hp := profileSplitPoint_bounds (A := A) hq hs.2 hlong
    exact profileHeight_nonneg (le_refl _) (by omega)
  | highFrequency a t v hlong hleft hvlo hvhi =>
    have hp := profileSplitPoint_bounds (A := A) hq hs.2 hlong
    exact profileHeight_nonneg (by omega) (le_refl _)
  | refine b e a v hlong test htest hlargest hlarge =>
    exact profileHeight_nonneg (Finset.mem_filter.mp htest).2.le (le_refl _)
  | _ => simp only [ProfileChainMove.budgetCost, le_refl]

/-- The actual longest-test origin pays the refinement upper cost. -/
theorem profileRefinement_budget_gain {A : ℕ → ℝ} {q N δ b e a v : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) (hs : (ProfileChainState.fourier b e a v).Valid N δ)
    (hlong : 100 * q < v - a) {test : ProfileScheduleTest}
    (htest : test ∈ profileRemainingTests A q N b e a)
    (hlarge : v - a ≤ 2 * test.length) :
    40 * q < v - test.anchor ∧ profileHeight A test.anchor a test.anchor ≤
      profileBudget A q test.anchor v - profileBudget A q a v := by
  obtain ⟨_, _, _, heN, hev⟩ := hs
  obtain ⟨hlist, hstart⟩ := Finset.mem_filter.mp htest
  obtain ⟨a', t', _, ht'e, horigin, hanchor, _, hlenanchor, hleft, hright, _, _⟩ :=
    profileScheduledTests_origin hq heN hlist
  have hleft' : a' + test.length ≤ test.anchor := by omega
  have hgain := profileOrigin_left_budget_gain (cost := profileHeight A test.anchor a test.anchor)
    hq (ht'e.trans heN) horigin hlong hδq hlarge
    (by rwa [← hanchor]) (by rwa [← hanchor]) (by rwa [← hanchor]) (ht'e.trans hev)
    (by rw [← hanchor])
  simpa only [← hanchor] using hgain

/-- Lemma 8.6(a), for every actual positive-cost transition. -/
theorem ProfileChainMove.positive_budgetCost_paid {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) {s u : ProfileChainState} (hs : s.Valid N δ)
    (move : ProfileChainMove A q N δ s u) (hcost : 0 < move.budgetCost) :
    40 * q < u.finish - u.start ∧ move.budgetCost ≤
      profileBudget A q u.start u.finish - profileBudget A q s.start s.finish := by
  cases move with
  | linearize a t hlong hright =>
    have hgain := profileSplitPoint_right_budget_gain hq hs.2 hlong hright
    exact ⟨by change 40 * q < profileSplitPoint A q N a t - a; omega, hgain.2⟩
  | highFrequency a t v hlong hleft hvlo hvhi =>
    exact profileSplitPoint_left_budget_gain hq hs.2 hlong hδq hleft hvlo hvhi
  | refine b e a v hlong test htest hlargest hlarge =>
    exact profileRefinement_budget_gain hq hδq hs hlong htest hlarge
  | _ => simp only [ProfileChainMove.budgetCost, lt_self_iff_false] at hcost

/-- Every move to a child of length at least `10q` pays its actual budget cost. -/
theorem ProfileChainMove.budgetCost_paid {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) {s u : ProfileChainState} (hs : s.Valid N δ)
    (move : ProfileChainMove A q N δ s u) (hchild : 10 * q ≤ u.finish - u.start) :
    move.budgetCost ≤ profileBudget A q u.start u.finish -
      profileBudget A q s.start s.finish := by
  by_cases hcost : 0 < move.budgetCost
  · exact (move.positive_budgetCost_paid hq hδq hs hcost).2
  · have hzero : move.budgetCost = 0 :=
      le_antisymm (le_of_not_gt hcost) (move.budgetCost_nonneg hq hs)
    have hnested := move.nested_valid hq hδq hs
    have hlength : u.start + 10 * q ≤ u.finish := by omega
    have hmono := profileBudget_mono (A := A) hnested.1 hlength hnested.2.1
    rw [hzero]
    linarith

end FalconerThetaGauge
