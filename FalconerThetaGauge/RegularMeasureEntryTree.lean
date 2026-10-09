/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChildren

/-!
# The actual finite induction tree

Nodes are concrete finite chains. Each level enumerates every child state
of the preceding level, choosing a genuine transition to append. The
short-chain bound makes all levels beyond the rounded depth empty.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

namespace ProfileMoveChain

/-- The root of an actual induction tree, as a chain with no transitions. -/
def root {A : ℕ → ℝ} {q N δ : ℕ} (s : ProfileChainState) (hs : s.Valid N δ) :
    ProfileMoveChain A q N δ where
  length := 0
  state := fun _ ↦ s
  step i hi := (by omega : False).elim
  valid_initial := hs

/-- Appending one actual transition retains the whole existing chain. -/
def append {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)
    (u : ProfileChainState) (move : ProfileChainMove A q N δ (chain.state chain.length) u) :
    ProfileMoveChain A q N δ where
  length := chain.length + 1
  state := fun i ↦ if i ≤ chain.length then chain.state i else u
  step i hi := by
    by_cases hbefore : i < chain.length
    · have hi₀ : i ≤ chain.length := by omega
      have hi₁ : i + 1 ≤ chain.length := by omega
      simpa only [hi₀, hi₁, ite_true] using chain.step i hbefore
    · have heq : i = chain.length := by omega
      subst i
      simpa only [le_refl, ite_true, show ¬chain.length + 1 ≤ chain.length by omega, ite_false]
        using move
  valid_initial := by simpa only [Nat.zero_le, ite_true] using chain.valid_initial

/-- Every actual child state contributes its concretely appended chain. -/
def children {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ) :
    Finset (ProfileMoveChain A q N δ) :=
  (profileChildStates A q N δ (chain.state chain.length)).attach.image (fun u ↦
    chain.append u.val (Classical.choice (profileChildStates_move u.property)))

theorem children_length {A : ℕ → ℝ} {q N δ : ℕ} {chain child : ProfileMoveChain A q N δ}
    (hchild : child ∈ chain.children) : child.length = chain.length + 1 := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hchild
  rfl

/-- The concrete list of appended chains obeys the actual branch bound. -/
theorem children_card_le {A : ℕ → ℝ} {q N δ : ℕ} (hq : 0 < q) (hδq : δ ≤ q)
    (chain : ProfileMoveChain A q N δ) : chain.children.card ≤ N + 13 := by
  have hcard := Finset.card_image_le
    (s := (profileChildStates A q N δ (chain.state chain.length)).attach)
    (f := fun u ↦ chain.append u.val (Classical.choice (profileChildStates_move u.property)))
  simp only [Finset.card_attach] at hcard
  exact hcard.trans (profileChildStates_card_le_source_bound hq
    (chain.state_valid hq hδq (le_refl chain.length)))

end ProfileMoveChain

/-- The actual nodes at a given generation of the induction tree. -/
def profileInductionLevel (A : ℕ → ℝ) (q N δ : ℕ) (s : ProfileChainState)
    (hs : s.Valid N δ) : ℕ → Finset (ProfileMoveChain A q N δ)
  | 0 => {ProfileMoveChain.root s hs}
  | m + 1 => (profileInductionLevel A q N δ s hs m).biUnion ProfileMoveChain.children

/-- Every enumerated node has its actual generation as its chain length. -/
theorem profileInductionLevel_length {A : ℕ → ℝ} {q N δ : ℕ} {s : ProfileChainState}
    (hs : s.Valid N δ) {m : ℕ} {chain : ProfileMoveChain A q N δ}
    (hchain : chain ∈ profileInductionLevel A q N δ s hs m) : chain.length = m := by
  induction m generalizing chain with
  | zero =>
    have heq : chain = ProfileMoveChain.root s hs := Finset.mem_singleton.mp hchain
    subst chain
    rfl
  | succ m ih =>
    obtain ⟨parent, hparent, hchild⟩ := Finset.mem_biUnion.mp hchain
    exact (ProfileMoveChain.children_length hchild).trans (by rw [ih hparent])

/-- Each actual level has at most the literal branch factor to the generation power. -/
theorem profileInductionLevel_card_le {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) {s : ProfileChainState} (hs : s.Valid N δ) (m : ℕ) :
    (profileInductionLevel A q N δ s hs m).card ≤ (N + 13) ^ m := by
  induction m with
  | zero => simp only [profileInductionLevel, Finset.card_singleton, pow_zero, le_refl]
  | succ m ih =>
    calc
      _ ≤ ∑ chain ∈ profileInductionLevel A q N δ s hs m, chain.children.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ chain ∈ profileInductionLevel A q N δ s hs m, (N + 13) :=
        Finset.sum_le_sum (fun chain _ ↦ chain.children_card_le hq hδq)
      _ = (profileInductionLevel A q N δ s hs m).card * (N + 13) := by simp
      _ ≤ (N + 13) ^ m * (N + 13) := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

/-- The literal finite depth cutoff, derived from the actual short-chain count. -/
def profileInductionDepth (θ : ℝ) (N : ℕ) : ℕ :=
  ⌊7 / blockParameter θ N + 1 / tolerance θ N⌋₊

/-- Every actual tree level beyond the derived finite cutoff is empty. -/
theorem profileInductionLevel_eq_empty {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState}
    (hs : s.Valid N (toleranceCount θ N)) {m : ℕ} (hm : profileInductionDepth θ N < m) :
    profileInductionLevel A (blockCount θ N) N (toleranceCount θ N) s hs m = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro chain hchain
  have hlength := profileInductionLevel_length hs hchain
  have hbound := chain.length_le_seven_inverse_block_add_inverse_tolerance hpar
  rw [hlength] at hbound
  have hfloor : m ≤ profileInductionDepth θ N := Nat.le_floor hbound
  omega

/-- The actual finite set of every node needed to unfold the induction. -/
def profileInductionNodes (A : ℕ → ℝ) (θ : ℝ) (N : ℕ) (s : ProfileChainState)
    (hs : s.Valid N (toleranceCount θ N)) :
    Finset (ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)) :=
  (range (profileInductionDepth θ N + 1)).biUnion (fun m ↦
    profileInductionLevel A (blockCount θ N) N (toleranceCount θ N) s hs m)

/-- The elementary finite geometric sum is bounded by the next base's power. -/
theorem sum_range_pow_le_add_one_pow (B d : ℕ) :
    ∑ m ∈ range (d + 1), B ^ m ≤ (B + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have hpow : B ^ d ≤ (B + 1) ^ d := Nat.pow_le_pow_left (by omega) d
    rw [pow_succ B d, pow_succ (B + 1) d]
    nlinarith

/-- The concrete induction tree has at most the actual branch-count power in Section 8.5. -/
theorem profileInductionNodes_card_le {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState} (hs : s.Valid N (toleranceCount θ N)) :
    (profileInductionNodes A θ N s hs).card ≤ (N + 14) ^ profileInductionDepth θ N := by
  have hN : 0 < N := by have := hpar.1; omega
  calc
    _ ≤ ∑ m ∈ range (profileInductionDepth θ N + 1),
        (profileInductionLevel A (blockCount θ N) N (toleranceCount θ N) s hs m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ m ∈ range (profileInductionDepth θ N + 1), (N + 13) ^ m :=
      Finset.sum_le_sum (fun m _ ↦ profileInductionLevel_card_le (blockCount_pos θ hN)
        (toleranceCount_le_blockCount_of_parameterFacts hpar) hs m)
    _ ≤ (N + 13 + 1) ^ profileInductionDepth θ N := sum_range_pow_le_add_one_pow _ _
    _ = _ := rfl

/-- The actual finite induction tree has at most `R^κ` nodes. -/
theorem profileInductionNodes_card_le_block_power {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState} (hs : s.Valid N (toleranceCount θ N)) :
    ((profileInductionNodes A θ N s hs).card : ℝ) ≤
      (2 : ℝ) ^ (blockParameter θ N * N) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have hε := tolerance_pos θ hN
  have hfloor : (profileInductionDepth θ N : ℝ) ≤
      7 / blockParameter θ N + 1 / tolerance θ N := Nat.floor_le (by positivity)
  have hcount := profileInductionNodes_card_le (A := A) hpar hs
  have hcount' : ((profileInductionNodes A θ N s hs).card : ℝ) ≤
      ((N : ℝ) + 14) ^ profileInductionDepth θ N := by exact_mod_cast hcount
  calc
    _ ≤ ((N : ℝ) + 14) ^ profileInductionDepth θ N := hcount'
    _ ≤ ((N : ℝ) + 14) ^ (7 / blockParameter θ N + 1 / tolerance θ N + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by linarith)
    _ ≤ _ := parameter_tree_node_bound hpar

/-- The concrete root chain occurs in the actual node set. -/
theorem profileInductionNodes_root_mem {A : ℕ → ℝ} {θ : ℝ} {N : ℕ}
    {s : ProfileChainState} (hs : s.Valid N (toleranceCount θ N)) :
    ProfileMoveChain.root s hs ∈ profileInductionNodes A θ N s hs := by
  exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (by omega),
    Finset.mem_singleton_self _⟩

/-- Every actual child of every enumerated node is itself an enumerated node. -/
theorem profileInductionNodes_children_subset {θ : ℝ} {N : ℕ} {A : ℕ → ℝ}
    (hpar : ParameterFacts θ N) {s : ProfileChainState} (hs : s.Valid N (toleranceCount θ N))
    {chain : ProfileMoveChain A (blockCount θ N) N (toleranceCount θ N)}
    (hchain : chain ∈ profileInductionNodes A θ N s hs) :
    chain.children ⊆ profileInductionNodes A θ N s hs := by
  obtain ⟨m, hm, hlevel⟩ := Finset.mem_biUnion.mp hchain
  intro child hchild
  have hlength := profileInductionLevel_length hs hlevel
  have hchildlength := ProfileMoveChain.children_length hchild
  have hbound := child.length_le_seven_inverse_block_add_inverse_tolerance hpar
  have hfloor : child.length ≤ profileInductionDepth θ N := Nat.le_floor hbound
  refine Finset.mem_biUnion.mpr ⟨m + 1, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_biUnion.mpr ⟨chain, hlevel, hchild⟩

/-- Each enumerated node begins at the actual root state. -/
theorem profileInductionLevel_initial {A : ℕ → ℝ} {q N δ : ℕ} {s : ProfileChainState}
    (hs : s.Valid N δ) {m : ℕ} {chain : ProfileMoveChain A q N δ}
    (hchain : chain ∈ profileInductionLevel A q N δ s hs m) : chain.state 0 = s := by
  induction m generalizing chain with
  | zero =>
    have heq : chain = ProfileMoveChain.root s hs := Finset.mem_singleton.mp hchain
    subst chain
    rfl
  | succ m ih =>
    obtain ⟨parent, hparent, hchild⟩ := Finset.mem_biUnion.mp hchain
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hchild
    simpa only [ProfileMoveChain.append, Nat.zero_le, ite_true] using ih hparent

/-- Every long state has an actual child in the finite enumeration. -/
theorem profileChildStates_nonempty_of_long {A : ℕ → ℝ} {q N δ : ℕ} (hq : 0 < q)
    {s : ProfileChainState} (hlong : 100 * q < s.finish - s.start) :
    (profileChildStates A q N δ s).Nonempty := by
  simp only [profileChildStates, hlong, ite_true]
  cases s with
  | discrepancy a t =>
    by_cases hright : a + t < 2 * profileSplitPoint A q N a t
    · simp only [profileLongChildStates, hright, ite_true, Finset.singleton_nonempty]
    · simp only [profileLongChildStates, hright, ite_false]
      exact ⟨.discrepancy a (t - δ), Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
  | fourier b e a v =>
    by_cases hlarge : v - a ≤ 2 * profileLongestTestLength A q N b e a
    · have hLpos : 0 < profileLongestTestLength A q N b e a := by
        change 100 * q < v - a at hlong
        omega
      obtain ⟨test, htest, hlen⟩ := profileLongestTestLength_attained hLpos
      simp only [profileLongChildStates, hlarge, ite_true]
      exact ⟨.fourier b e test.anchor v, Finset.mem_image.mpr
        ⟨test, Finset.mem_filter.mpr ⟨htest, hlen⟩, rfl⟩⟩
    · simp only [profileLongChildStates, hlarge, ite_false]
      exact ⟨.fourier b e (profileNearStart A q N δ b e a v) v,
        Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩

/-- The actual finite enumeration has no children exactly at the short states. -/
theorem profileChildStates_eq_empty_iff_short {A : ℕ → ℝ} {q N δ : ℕ} (hq : 0 < q)
    (s : ProfileChainState) :
    profileChildStates A q N δ s = ∅ ↔ s.finish - s.start ≤ 100 * q := by
  constructor
  · intro hempty
    by_contra h
    have hnonempty := profileChildStates_nonempty_of_long (A := A) (N := N) (δ := δ)
      hq (lt_of_not_ge h)
    rw [hempty] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  · intro hshort
    simp only [profileChildStates, not_lt.mpr hshort, ite_false]

end FalconerThetaGauge
