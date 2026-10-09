/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryTreeLevels

/-!
# Counting actual induction nodes with path multiplicities

The multiset enumeration keeps every recurrence branch when paths meet.
Its full cardinality, including these repetitions, is still at most `R^κ`.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The actual nodes at one generation, retaining every path multiplicity. -/
def profileInductionLevelVisits (A : ℕ → ℝ) (q N δ : ℕ) (s : ProfileChainState)
    (hs : s.Valid N δ) : ℕ → Multiset (ProfileMoveChain A q N δ)
  | 0 => {ProfileMoveChain.root s hs}
  | m + 1 => (profileInductionLevelVisits A q N δ s hs m).bind (fun chain ↦ chain.children.val)

theorem profileInductionLevelVisits_length {A : ℕ → ℝ} {q N δ : ℕ} {s : ProfileChainState}
    (hs : s.Valid N δ) {m : ℕ} {chain : ProfileMoveChain A q N δ}
    (hchain : chain ∈ profileInductionLevelVisits A q N δ s hs m) : chain.length = m := by
  induction m generalizing chain with
  | zero =>
    have heq : chain = ProfileMoveChain.root s hs := Multiset.mem_singleton.mp hchain
    subst chain
    rfl
  | succ m ih =>
    obtain ⟨parent, hparent, hchild⟩ := Multiset.mem_bind.mp hchain
    exact (ProfileMoveChain.children_length hchild).trans (by rw [ih hparent])

/-- Even after counting every path separately, the actual level obeys the branch power bound. -/
theorem profileInductionLevelVisits_card_le {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) {s : ProfileChainState} (hs : s.Valid N δ) (m : ℕ) :
    (profileInductionLevelVisits A q N δ s hs m).card ≤ (N + 13) ^ m := by
  induction m with
  | zero => simp only [profileInductionLevelVisits, Multiset.card_singleton, pow_zero, le_refl]
  | succ m ih =>
    simp only [profileInductionLevelVisits, Multiset.card_bind]
    have hsum := Multiset.sum_le_card_nsmul
      ((profileInductionLevelVisits A q N δ s hs m).map (fun chain ↦ chain.children.card))
      (N + 13) (by
        intro c hc
        obtain ⟨chain, _, rfl⟩ := Multiset.mem_map.mp hc
        exact chain.children_card_le hq hδq)
    simp only [Multiset.card_map, nsmul_eq_mul] at hsum
    calc
      _ ≤ (profileInductionLevelVisits A q N δ s hs m).card * (N + 13) := hsum
      _ ≤ (N + 13) ^ m * (N + 13) := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

/-- The concrete multiplicity-preserving node enumeration also stops at the derived cutoff. -/
theorem profileInductionLevelVisits_eq_zero {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState}
    (hs : s.Valid N (toleranceCount θ N)) {m : ℕ} (hm : profileInductionDepth θ N < m) :
    profileInductionLevelVisits A (blockCount θ N) N (toleranceCount θ N) s hs m = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro chain hchain
  have hlength := profileInductionLevelVisits_length hs hchain
  have hbound := chain.length_le_seven_inverse_block_add_inverse_tolerance hpar
  rw [hlength] at hbound
  have hfloor : m ≤ profileInductionDepth θ N := Nat.le_floor hbound
  omega

/-- The actual finite multiset of all node visits in the recurrence tree. -/
def profileInductionVisits (A : ℕ → ℝ) (θ : ℝ) (N : ℕ) (s : ProfileChainState)
    (hs : s.Valid N (toleranceCount θ N)) :
    Multiset (ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :=
  ∑ m ∈ range (profileInductionDepth θ N + 1),
    profileInductionLevelVisits A (blockCount θ N) N (toleranceCount θ N) s hs m

/-- The actual recurrence visits, with every path counted, satisfy the literal tree bound. -/
theorem profileInductionVisits_card_le {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState} (hs : s.Valid N (toleranceCount θ N)) :
    (profileInductionVisits A θ N s hs).card ≤ (N + 14) ^ profileInductionDepth θ N := by
  have hN : 0 < N := by have := hpar.1; omega
  unfold profileInductionVisits
  rw [Multiset.card_sum]
  calc
    _ ≤ ∑ m ∈ range (profileInductionDepth θ N + 1), (N + 13) ^ m :=
      Finset.sum_le_sum (fun m _ ↦ profileInductionLevelVisits_card_le (blockCount_pos θ hN)
        (toleranceCount_le_blockCount_of_parameterFacts hpar) hs m)
    _ ≤ (N + 13 + 1) ^ profileInductionDepth θ N := sum_range_pow_le_add_one_pow _ _
    _ = _ := rfl

/-- Counting repeated paths costs at most `R^κ` in the actual finite recurrence tree. -/
theorem profileInductionVisits_card_le_block_power {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState} (hs : s.Valid N (toleranceCount θ N)) :
    ((profileInductionVisits A θ N s hs).card : ℝ) ≤
      (2 : ℝ) ^ (blockParameter θ N * N) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have hε := tolerance_pos θ hN
  have hfloor : (profileInductionDepth θ N : ℝ) ≤
      7 / blockParameter θ N + 1 / tolerance θ N := Nat.floor_le (by positivity)
  have hcount := profileInductionVisits_card_le (A := A) hpar hs
  have hcount' : ((profileInductionVisits A θ N s hs).card : ℝ) ≤
      ((N : ℝ) + 14) ^ profileInductionDepth θ N := by exact_mod_cast hcount
  calc
    _ ≤ ((N : ℝ) + 14) ^ profileInductionDepth θ N := hcount'
    _ ≤ ((N : ℝ) + 14) ^ (7 / blockParameter θ N + 1 / tolerance θ N + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by linarith)
    _ ≤ _ := parameter_tree_node_bound hpar

end FalconerThetaGauge
