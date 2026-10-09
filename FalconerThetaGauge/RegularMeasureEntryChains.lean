/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainSteps

/-!
# Finite chains of the actual induction moves

The chain contains concrete states and genuine transitions. Its start depths
increase, its end depths decrease, and visits or crossings of marked depths
are counted injectively.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- A finite chain of the actual six child types of Table 1. -/
structure ProfileMoveChain (A : ℕ → ℝ) (q N δ : ℕ) where
  length : ℕ
  state : ℕ → ProfileChainState
  step (i : ℕ) (hi : i < length) : ProfileChainMove A q N δ (state i) (state (i + 1))
  valid_initial : (state 0).Valid N δ

namespace ProfileMoveChain

variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)

/-- The transition's child-type number, extended by zero beyond the finite chain. -/
def tag (i : ℕ) : ℕ := if hi : i < chain.length then (chain.step i hi).tag else 0

theorem tag_eq {i : ℕ} (hi : i < chain.length) : chain.tag i = (chain.step i hi).tag := by
  simp only [tag, hi, dite_eq_left]

/-- The actual indices of moves with a given child type. -/
def movesOfTag (k : ℕ) : Finset ℕ := (range chain.length).filter (fun i ↦ chain.tag i = k)

/-- The actual indices of the two moves to a marked start depth. -/
def markedMoves : Finset ℕ :=
  (range chain.length).filter (fun i ↦ chain.tag i = 2 ∨ chain.tag i = 3)

/-- The actual indices whose increasing start interval crosses some marked depth. -/
def crossingMoves : Finset ℕ := (range chain.length).filter (fun i ↦
  ∃ p ∈ profileMarkedDepths A q N, (chain.state i).start < p ∧ p ≤ (chain.state (i + 1)).start)

theorem state_valid (hq : 0 < q) (hδq : δ ≤ q) {i : ℕ} (hi : i ≤ chain.length) :
    (chain.state i).Valid N δ := by
  induction i with
  | zero => exact chain.valid_initial
  | succ i ih =>
    exact ((chain.step i (by omega)).nested_valid hq hδq (ih (by omega))).2.2

theorem starts_monotone (hq : 0 < q) (hδq : δ ≤ q) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ chain.length) : (chain.state i).start ≤ (chain.state j).start := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans
      ((chain.step j (by omega)).nested_valid hq hδq (chain.state_valid hq hδq (by omega))).1

theorem ends_antitone (hq : 0 < q) (hδq : δ ≤ q) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ chain.length) : (chain.state j).finish ≤ (chain.state i).finish := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    exact ((chain.step j (by omega)).nested_valid hq hδq
      (chain.state_valid hq hδq (by omega))).2.1.trans (ih (by omega))

/-- Different marked-start moves arrive at different marked depths. -/
theorem markedMoves_card_le (hq : 0 < q) (hδq : δ ≤ q) :
    chain.markedMoves.card ≤ (profileMarkedDepths A q N).card := by
  apply Finset.card_le_card_of_injOn (fun i ↦ (chain.state (i + 1)).start)
  · intro i hi
    obtain ⟨hi, htag⟩ := Finset.mem_filter.mp hi
    have hi' := Finset.mem_range.mp hi
    rw [chain.tag_eq hi'] at htag
    exact ((chain.step i hi').marked_start hq (chain.state_valid hq hδq (by omega)) htag).2
  · intro i hi j hj heq
    change (chain.state (i + 1)).start = (chain.state (j + 1)).start at heq
    obtain ⟨hi, htagi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj, htagj⟩ := Finset.mem_filter.mp hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [chain.tag_eq hi'] at htagi
    rw [chain.tag_eq hj'] at htagj
    have his := ((chain.step i hi').marked_start hq
      (chain.state_valid hq hδq (by omega)) htagi).1
    have hjs := ((chain.step j hj').marked_start hq
      (chain.state_valid hq hδq (by omega)) htagj).1
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hmono := chain.starts_monotone hq hδq (i := i + 1) (j := j) (by omega) (by omega)
      omega
    · rfl
    · have hmono := chain.starts_monotone hq hδq (i := j + 1) (j := i) (by omega) (by omega)
      omega

theorem movesOfTag_two_card_le (hq : 0 < q) (hδq : δ ≤ q) :
    (chain.movesOfTag 2).card ≤ (profileMarkedDepths A q N).card := by
  apply (Finset.card_le_card ?_).trans (chain.markedMoves_card_le hq hδq)
  intro i hi
  obtain ⟨hi, htag⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, Or.inl htag⟩

theorem movesOfTag_three_card_le (hq : 0 < q) (hδq : δ ≤ q) :
    (chain.movesOfTag 3).card ≤ (profileMarkedDepths A q N).card := by
  apply (Finset.card_le_card ?_).trans (chain.markedMoves_card_le hq hδq)
  intro i hi
  obtain ⟨hi, htag⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, Or.inr htag⟩

/-- An increasing start can cross each marked depth during at most one step. -/
theorem crossingMoves_card_le (hq : 0 < q) (hδq : δ ≤ q) :
    chain.crossingMoves.card ≤ (profileMarkedDepths A q N).card := by
  let witness (i : ℕ) : ℕ := if hi : i ∈ chain.crossingMoves then
    (Finset.mem_filter.mp hi).2.choose else 0
  have hw {i : ℕ} (hi : i ∈ chain.crossingMoves) :
      witness i ∈ profileMarkedDepths A q N ∧ (chain.state i).start < witness i ∧
        witness i ≤ (chain.state (i + 1)).start := by
    simp only [witness, hi, dite_eq_left]
    exact (Finset.mem_filter.mp hi).2.choose_spec
  apply Finset.card_le_card_of_injOn witness
  · intro i hi
    exact (hw hi).1
  · intro i hi j hj heq
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hwi := hw hi
    have hwj := hw hj
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hmono := chain.starts_monotone hq hδq (i := i + 1) (j := j) (by omega) (by omega)
      omega
    · rfl
    · have hmono := chain.starts_monotone hq hδq (i := j + 1) (j := i) (by omega) (by omega)
      omega

/-- Exact telescoping of the actual decreases in interval ends. -/
theorem sum_end_drops (hq : 0 < q) (hδq : δ ≤ q) {m : ℕ} (hm : m ≤ chain.length) :
    ∑ i ∈ range m, ((chain.state i).finish - (chain.state (i + 1)).finish) =
      (chain.state 0).finish - (chain.state m).finish := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h₀ := chain.ends_antitone hq hδq (i := 0) (j := m) (by omega) (by omega)
    have h₁ := chain.ends_antitone hq hδq (i := m) (j := m + 1) (by omega) hm
    omega

/-- A family of actual moves dropping the end by `d` has size at most the total depth divided
by `d`, expressed without division so that the exact integer estimate is retained. -/
theorem moves_card_mul_drop_le (hq : 0 < q) (hδq : δ ≤ q) (S : Finset ℕ) (d : ℕ)
    (hS : S ⊆ range chain.length)
    (hdrop : ∀ i ∈ S, d ≤ (chain.state i).finish - (chain.state (i + 1)).finish) :
    S.card * d ≤ N := by
  have hN : (chain.state 0).finish ≤ N := by
    cases hs : chain.state 0 with
    | discrepancy a t => exact (hs ▸ chain.valid_initial).2
    | fourier b e a v =>
      exact (hs ▸ chain.valid_initial).2.2.1.trans (hs ▸ chain.valid_initial).2.2.2.1
  calc
    _ = ∑ i ∈ S, d := by simp
    _ ≤ ∑ i ∈ S, ((chain.state i).finish - (chain.state (i + 1)).finish) :=
      Finset.sum_le_sum hdrop
    _ ≤ ∑ i ∈ range chain.length,
        ((chain.state i).finish - (chain.state (i + 1)).finish) :=
      Finset.sum_le_sum_of_subset hS
    _ = (chain.state 0).finish - (chain.state chain.length).finish :=
      chain.sum_end_drops hq hδq (le_refl _)
    _ ≤ N := (Nat.sub_le _ _).trans hN

theorem linearize_card_mul_block_le (hq : 0 < q) (hδq : δ ≤ q) :
    (chain.movesOfTag 0).card * q ≤ N := by
  apply chain.moves_card_mul_drop_le hq hδq _ q (Finset.filter_subset _ _)
  intro i hi
  obtain ⟨hi, htag⟩ := Finset.mem_filter.mp hi
  have hi' := Finset.mem_range.mp hi
  rw [chain.tag_eq hi'] at htag
  exact (chain.step i hi').linearize_end_drop hq
    (chain.state_valid hq hδq (by omega)) htag

theorem lowFrequency_card_mul_thickness_le (hq : 0 < q) (hδq : δ ≤ q) :
    (chain.movesOfTag 1).card * δ ≤ N := by
  apply chain.moves_card_mul_drop_le hq hδq _ δ (Finset.filter_subset _ _)
  intro i hi
  obtain ⟨hi, htag⟩ := Finset.mem_filter.mp hi
  have hi' := Finset.mem_range.mp hi
  rw [chain.tag_eq hi'] at htag
  exact (chain.step i hi').lowFrequency_end_drop hδq
    (chain.state_valid hq hδq (by omega)) htag

end ProfileMoveChain

end FalconerThetaGauge
