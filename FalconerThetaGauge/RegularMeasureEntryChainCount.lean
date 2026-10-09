/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChains

/-!
# Counting every actual child type along a chain

Fourier-state entries pay for far exits. The concrete longest-test alternative
pays for near moves by marked-depth crossings, following refinements, or the
last move. Together with the exact end-drop bounds, this proves Lemma 8.7.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- Exact conservation of Fourier-state entries and exits during each actual move. -/
theorem ProfileChainMove.fourier_balance {A : ℕ → ℝ} {q N δ : ℕ}
    {s u : ProfileChainState} (move : ProfileChainMove A q N δ s u) :
    (if u.isFourier then 1 else 0) + (if move.tag = 5 then 1 else 0) =
      (if s.isFourier then 1 else 0) + (if move.tag = 2 then 1 else 0) := by
  cases move <;> simp [ProfileChainState.isFourier, ProfileChainMove.tag]

namespace ProfileMoveChain

variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)

theorem prefix_tag_count_succ (m k : ℕ) :
    ((range (m + 1)).filter (fun i ↦ chain.tag i = k)).card =
      ((range m).filter (fun i ↦ chain.tag i = k)).card +
        (if chain.tag m = k then 1 else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases htag : chain.tag m = k <;> simp [htag]

/-- The exact finite conservation law counts actual far exits and high-frequency entries. -/
theorem prefix_fourier_balance {m : ℕ} (hm : m ≤ chain.length) :
    ((range m).filter (fun i ↦ chain.tag i = 5)).card +
        (if (chain.state m).isFourier then 1 else 0) =
      ((range m).filter (fun i ↦ chain.tag i = 2)).card +
        (if (chain.state 0).isFourier then 1 else 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [chain.prefix_tag_count_succ m 5, chain.prefix_tag_count_succ m 2]
    have hflow := (chain.step m (by omega)).fourier_balance
    rw [← chain.tag_eq (by omega)] at hflow
    have hprevious := ih (by omega)
    omega

/-- Each Fourier run has at most one actual far exit. -/
theorem far_card_le_highFrequency_add_one :
    (chain.movesOfTag 5).card ≤ (chain.movesOfTag 2).card + 1 := by
  have hbalance := chain.prefix_fourier_balance (le_refl chain.length)
  change ((range chain.length).filter (fun i ↦ chain.tag i = 5)).card ≤
    ((range chain.length).filter (fun i ↦ chain.tag i = 2)).card + 1
  split_ifs at hbalance <;> omega

/-- The actual indices immediately preceding a refinement. -/
def beforeRefinementMoves : Finset ℕ :=
  (range chain.length).filter (fun i ↦ i + 1 < chain.length ∧ chain.tag (i + 1) = 3)

theorem beforeRefinementMoves_card_le :
    chain.beforeRefinementMoves.card ≤ (chain.movesOfTag 3).card := by
  apply Finset.card_le_card_of_injOn (fun i ↦ i + 1)
  · intro i hi
    obtain ⟨_, hnext, htag⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnext, htag⟩
  · intro i hi j hj heq
    simpa using heq

/-- The actual near moves are covered by anchor crossings, following refinements, and
the final index. No assumption about the number of these alternatives is used. -/
theorem near_moves_cover (hq : 0 < q) (hδq : δ ≤ q) :
    chain.movesOfTag 4 ⊆ chain.crossingMoves ∪ chain.beforeRefinementMoves ∪
      {chain.length - 1} := by
  intro i hi
  obtain ⟨hi, htag⟩ := Finset.mem_filter.mp hi
  have hi' := Finset.mem_range.mp hi
  by_cases hnext : i + 1 < chain.length
  · rw [chain.tag_eq hi'] at htag
    have hcase := (chain.step i hi').near_next hq hδq
      (chain.state_valid hq hδq (by omega)) htag (chain.step (i + 1) hnext)
    apply Finset.mem_union_left
    rcases hcase with hcross | hrefine
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hcross⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hi, hnext, by rwa [chain.tag_eq hnext]⟩
  · apply Finset.mem_union_right
    exact Finset.mem_singleton.mpr (by omega)

/-- At most two marked-depth counts plus one near move occur along an actual chain. -/
theorem near_card_le (hq : 0 < q) (hδq : δ ≤ q) :
    (chain.movesOfTag 4).card ≤ 2 * (profileMarkedDepths A q N).card + 1 := by
  have hcover := Finset.card_le_card (chain.near_moves_cover hq hδq)
  have h₁ := Finset.card_union_le chain.crossingMoves chain.beforeRefinementMoves
  have h₂ := Finset.card_union_le (chain.crossingMoves ∪ chain.beforeRefinementMoves)
    {chain.length - 1}
  have hcross := chain.crossingMoves_card_le hq hδq
  have hbefore := chain.beforeRefinementMoves_card_le.trans
    (chain.movesOfTag_three_card_le hq hδq)
  simp only [Finset.card_singleton] at h₂
  omega

/-- The actual ordinary moves exclude precisely the low-frequency children. -/
def ordinaryMoves : Finset ℕ := (range chain.length).filter (fun i ↦ chain.tag i ≠ 1)

theorem ordinary_moves_cover :
    chain.ordinaryMoves ⊆ chain.movesOfTag 0 ∪ chain.markedMoves ∪
      chain.movesOfTag 4 ∪ chain.movesOfTag 5 := by
  intro i hi
  obtain ⟨hi, hnot⟩ := Finset.mem_filter.mp hi
  have hi' := Finset.mem_range.mp hi
  have hbound : chain.tag i ≤ 5 := by
    rw [chain.tag_eq hi']
    exact (chain.step i hi').tag_le_five
  have hcases : chain.tag i = 0 ∨ chain.tag i = 2 ∨ chain.tag i = 3 ∨
      chain.tag i = 4 ∨ chain.tag i = 5 := by omega
  rcases hcases with hzero | htwo | hthree | hfour | hfive
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hzero⟩)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, Or.inl htwo⟩)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, Or.inr hthree⟩)))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hfour⟩))
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hfive⟩)

/-- The finite ordinary count follows from the actual transition semantics. -/
theorem ordinary_card_le (hq : 0 < q) (hδq : δ ≤ q) :
    chain.ordinaryMoves.card ≤ (chain.movesOfTag 0).card +
      4 * (profileMarkedDepths A q N).card + 2 := by
  have hcover := Finset.card_le_card chain.ordinary_moves_cover
  have h₁ := Finset.card_union_le (chain.movesOfTag 0) chain.markedMoves
  have h₂ := Finset.card_union_le (chain.movesOfTag 0 ∪ chain.markedMoves) (chain.movesOfTag 4)
  have h₃ := Finset.card_union_le
    (chain.movesOfTag 0 ∪ chain.markedMoves ∪ chain.movesOfTag 4) (chain.movesOfTag 5)
  have hmarks := chain.markedMoves_card_le hq hδq
  have hnear := chain.near_card_le hq hδq
  have hfar := chain.far_card_le_highFrequency_add_one.trans
    (Nat.add_le_add_right (chain.movesOfTag_two_card_le hq hδq) 1)
  omega

end ProfileMoveChain

end FalconerThetaGauge
