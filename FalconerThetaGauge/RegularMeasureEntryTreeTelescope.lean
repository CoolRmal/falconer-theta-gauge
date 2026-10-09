module

public import FalconerThetaGauge.ScheduledStateEnergiesErrors
public import FalconerThetaGauge.RegularMeasureEntryTreeAppend

/-! # Multiplicity-preserving telescoping of the genuine finite induction tree -/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

theorem multiset_sum_map_finset_sum {α : Type*} (I : Finset ℕ) (m : ℕ → Multiset α)
    (f : α → ℝ) :
    ((∑ n ∈ I, m n).map f).sum = ∑ n ∈ I, ((m n).map f).sum := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert n I hn ih => simp [sum_insert hn, Multiset.map_add, ih]

theorem multiset_sum_map_filter_eq_ite {α : Type*} (m : Multiset α)
    (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    ((m.filter p).map f).sum = (m.map fun x ↦ if p x then f x else 0).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons x m ih => by_cases hx : p x <;> simp [hx, ih]

/-- Each repeated path is counted separately when the local inequalities telescope. -/
theorem profileInductionVisits_telescope {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState}
    (hs : s.Valid N (toleranceCount θ N))
    (f g : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N) → ℝ)
    (hg : ∀ chain ∈ profileInductionVisits A θ N s hs, 0 ≤ g chain)
    (hrec : ∀ chain ∈ profileInductionVisits A θ N s hs,
      100 * blockCount θ N < (chain.state chain.length).finish -
        (chain.state chain.length).start →
      f chain ≤ (chain.children.val.map f).sum + g chain) :
    f (ProfileMoveChain.root s hs) ≤
      ((profileTerminalLeafVisits A θ N s hs).map f).sum +
        ((profileInductionVisits A θ N s hs).map g).sum := by
  let D := profileInductionDepth θ N
  let level := profileInductionLevelVisits A (blockCount θ N) N
    (toleranceCount θ N) s hs
  let leaf := fun chain : ProfileMoveChain A (blockCount θ N) N
      (toleranceCount θ N) ↦
    if (chain.state chain.length).finish - (chain.state chain.length).start ≤
      100 * blockCount θ N then f chain else 0
  have hmem : ∀ m ≤ D, ∀ chain ∈ level m, chain ∈ profileInductionVisits A θ N s hs := by
    intro m hm chain hc
    exact Multiset.mem_sum.mpr ⟨m, mem_range.mpr (by omega), hc⟩
  have hstep : ∀ m ≤ D, ((level m).map f).sum ≤
      ((level (m + 1)).map f).sum + ((level m).map leaf).sum +
        ((level m).map g).sum := by
    intro m hm
    have hh := Multiset.sum_map_le_sum_map f
      (fun chain ↦ (chain.children.val.map f).sum + leaf chain + g chain)
      (s := level m) (by
        intro chain hc
        have hv := hmem m hm chain hc
        by_cases hshort : (chain.state chain.length).finish -
            (chain.state chain.length).start ≤ 100 * blockCount θ N
        · have hempty : chain.children = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro child hc'
            obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hc'
            obtain ⟨move⟩ := profileChildStates_move u.property
            have hl := move.long
            omega
          simp only [hempty, Finset.empty_val, Multiset.map_zero, Multiset.sum_zero,
            leaf, hshort, ite_true, zero_add]
          exact le_add_of_nonneg_right (hg chain hv)
        · have hr := hrec chain hv (by omega)
          simpa only [leaf, hshort, ite_false, add_zero] using hr)
    rw [Multiset.sum_map_add, Multiset.sum_map_add] at hh
    have hnext : ((level (m + 1)).map f).sum =
        ((level m).map fun chain ↦ (chain.children.val.map f).sum).sum := by
      change (((level m).bind fun chain ↦ chain.children.val).map f).sum = _
      rw [Multiset.map_bind, Multiset.sum_bind]
    rw [hnext]
    exact hh
  have htel : ∀ k ≤ D + 1, f (ProfileMoveChain.root s hs) ≤
      ((level k).map f).sum + (∑ m ∈ range k, ((level m).map leaf).sum) +
        ∑ m ∈ range k, ((level m).map g).sum := by
    intro k
    induction k with
    | zero => intro _; simp only [level, profileInductionLevelVisits,
        Multiset.map_singleton, Multiset.sum_singleton, range_zero, sum_empty, add_zero,
        le_refl]
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hm := hstep k (by omega)
      rw [sum_range_succ, sum_range_succ]
      linarith
  have hz : level (D + 1) = 0 := profileInductionLevelVisits_eq_zero hpar hs (by omega)
  have ht := htel (D + 1) (le_refl _)
  rw [hz, Multiset.map_zero, Multiset.sum_zero, zero_add] at ht
  have hf : ((profileTerminalLeafVisits A θ N s hs).map f).sum =
      ∑ m ∈ range (D + 1), ((level m).map leaf).sum := by
    unfold profileTerminalLeafVisits
    rw [multiset_sum_map_filter_eq_ite]
    exact multiset_sum_map_finset_sum (range (D + 1)) level leaf
  have he : ((profileInductionVisits A θ N s hs).map g).sum =
      ∑ m ∈ range (D + 1), ((level m).map g).sum :=
    multiset_sum_map_finset_sum (range (D + 1)) level g
  rw [hf, he]
  exact ht

end FalconerThetaGauge
