/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainMultipliers

/-!
# Concrete child enumeration and the branch bound

Every possible child in the six transition constructors belongs to this
actual finite enumeration. Longest-test ties are allowed, with duplicate
child states removed. Even this full enumeration has at most `N+1` children.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The actual near-child start depth for a Fourier state. -/
def profileNearStart (A : ℕ → ℝ) (q N δ b e a v : ℕ) : ℕ :=
  v - 2 * max (profileLongestTestLength A q N b e a) δ

/-- The finite enumeration of the applicable child states of a long parent. -/
def profileLongChildStates (A : ℕ → ℝ) (q N δ : ℕ) : ProfileChainState → Finset ProfileChainState
  | .discrepancy a t =>
      let p := profileSplitPoint A q N a t
      if a + t < 2 * p then {.discrepancy a p}
      else {.discrepancy a (t - δ)} ∪
        (Ioc (t - δ) t).image (fun v ↦ .fourier a t p v)
  | .fourier b e a v =>
      let L := profileLongestTestLength A q N b e a
      if v - a ≤ 2 * L then
        ((profileRemainingTests A q N b e a).filter (fun test ↦ test.length = L)).image
          (fun test ↦ .fourier b e test.anchor v)
      else {.fourier b e (profileNearStart A q N δ b e a v) v} ∪
        (Ioo a (min (v + 1) (profileNearStart A q N δ b e a v + 12))).image
          (fun n ↦ .discrepancy n v)

/-- The actual child enumeration, empty precisely when the state is short. -/
def profileChildStates (A : ℕ → ℝ) (q N δ : ℕ) (s : ProfileChainState) :
    Finset ProfileChainState :=
  if 100 * q < s.finish - s.start then profileLongChildStates A q N δ s else ∅

/-- Every enumerated child is connected to its parent by an actual Table 1 move. -/
theorem profileChildStates_move {A : ℕ → ℝ} {q N δ : ℕ} {s u : ProfileChainState}
    (hu : u ∈ profileChildStates A q N δ s) : Nonempty (ProfileChainMove A q N δ s u) := by
  have hlong : 100 * q < s.finish - s.start := by
    by_contra h
    simp only [profileChildStates, h, ite_false, Finset.notMem_empty] at hu
  simp only [profileChildStates, hlong, ite_true] at hu
  cases s with
  | discrepancy a t =>
    change 100 * q < t - a at hlong
    by_cases hright : a + t < 2 * profileSplitPoint A q N a t
    · simp only [profileLongChildStates, hright, ite_true, Finset.mem_singleton] at hu
      subst u
      exact ⟨.linearize a t hlong hright⟩
    · simp only [profileLongChildStates, hright, ite_false] at hu
      rcases Finset.mem_union.mp hu with hlow | hhigh
      · have heq := Finset.mem_singleton.mp hlow
        subst u
        exact ⟨.lowFrequency a t hlong (by omega)⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hhigh
        obtain ⟨hvlo, hvhi⟩ := Finset.mem_Ioc.mp hv
        exact ⟨.highFrequency a t v hlong (by omega) hvlo hvhi⟩
  | fourier b e a v =>
    change 100 * q < v - a at hlong
    by_cases hlarge : v - a ≤ 2 * profileLongestTestLength A q N b e a
    · simp only [profileLongChildStates, hlarge, ite_true] at hu
      obtain ⟨test, htest, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨htest, hlen⟩ := Finset.mem_filter.mp htest
      exact ⟨.refine b e a v hlong test htest hlen (by omega)⟩
    · simp only [profileLongChildStates, hlarge, ite_false] at hu
      rcases Finset.mem_union.mp hu with hnear | hfar
      · have heq := Finset.mem_singleton.mp hnear
        subst u
        exact ⟨.near b e a v hlong (by omega)⟩
      · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hfar
        obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioo.mp hn
        have hnhi' := min_le_right (v + 1) (profileNearStart A q N δ b e a v + 12)
        have hnv := min_le_left (v + 1) (profileNearStart A q N δ b e a v + 12)
        exact ⟨.far b e a v n hlong (by omega) hnlo (hnhi.trans_le hnhi') (by omega)⟩

/-- Every actual move is included in the concrete child enumeration. -/
theorem ProfileChainMove.mem_childStates {A : ℕ → ℝ} {q N δ : ℕ}
    {s u : ProfileChainState} (move : ProfileChainMove A q N δ s u) :
    u ∈ profileChildStates A q N δ s := by
  simp only [profileChildStates, move.long, ite_true]
  cases move with
  | linearize a t hlong hright =>
    simp [profileLongChildStates, hright]
  | lowFrequency a t hlong hleft =>
    have hright : ¬a + t < 2 * profileSplitPoint A q N a t := by omega
    simp [profileLongChildStates, hright]
  | highFrequency a t v hlong hleft hvlo hvhi =>
    have hright : ¬a + t < 2 * profileSplitPoint A q N a t := by omega
    simp only [profileLongChildStates, hright, ite_false]
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨v, Finset.mem_Ioc.mpr ⟨hvlo, hvhi⟩, rfl⟩)
  | refine b e a v hlong test htest hlargest hlarge =>
    have hlarge' : v - a ≤ 2 * profileLongestTestLength A q N b e a := by omega
    simp only [profileLongChildStates, hlarge', ite_true]
    exact Finset.mem_image.mpr ⟨test, Finset.mem_filter.mpr ⟨htest, hlargest⟩, rfl⟩
  | near b e a v hlong hsmall =>
    have hlarge : ¬v - a ≤ 2 * profileLongestTestLength A q N b e a := by omega
    simp [profileLongChildStates, hlarge, profileNearStart]
  | far b e a v n hlong hsmall hnlo hnhi hnv =>
    have hlarge : ¬v - a ≤ 2 * profileLongestTestLength A q N b e a := by omega
    simp only [profileLongChildStates, hlarge, ite_false]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨n, Finset.mem_Ioo.mpr ⟨hnlo, by
      change n < min (v + 1) (v - 2 * max (profileLongestTestLength A q N b e a) δ + 12)
      omega⟩, rfl⟩

/-- Every valid state has at most `N+1` distinct children, including every longest-test tie. -/
theorem profileChildStates_card_le {A : ℕ → ℝ} {q N δ : ℕ} (hq : 0 < q)
    {s : ProfileChainState} (hs : s.Valid N δ) :
    (profileChildStates A q N δ s).card ≤ N + 1 := by
  by_cases hlong : 100 * q < s.finish - s.start
  · simp only [profileChildStates, hlong, ite_true]
    cases s with
    | discrepancy a t =>
      obtain ⟨_, ht⟩ := hs
      by_cases hright : a + t < 2 * profileSplitPoint A q N a t
      · simp only [profileLongChildStates, hright, ite_true, Finset.card_singleton]
        omega
      · simp only [profileLongChildStates, hright, ite_false]
        have hcard := Finset.card_union_le ({.discrepancy a (t - δ)} : Finset ProfileChainState)
          ((Ioc (t - δ) t).image (fun v ↦ ProfileChainState.fourier a t
            (profileSplitPoint A q N a t) v))
        have himage := Finset.card_image_le (s := Ioc (t - δ) t)
          (f := fun v ↦ ProfileChainState.fourier a t (profileSplitPoint A q N a t) v)
        simp only [Finset.card_singleton, Nat.card_Ioc] at hcard himage
        omega
    | fourier b e a v =>
      obtain ⟨_, _, hve, heN, _⟩ := hs
      by_cases hlarge : v - a ≤ 2 * profileLongestTestLength A q N b e a
      · simp only [profileLongChildStates, hlarge, ite_true]
        have hsubset :
            ((profileRemainingTests A q N b e a).filter (fun test ↦
              test.length = profileLongestTestLength A q N b e a)).image
                (fun test ↦ ProfileChainState.fourier b e test.anchor v) ⊆
                  (range (N + 1)).image (fun p ↦ ProfileChainState.fourier b e p v) := by
          intro u hu
          obtain ⟨test, htest, rfl⟩ := Finset.mem_image.mp hu
          have hlist := (Finset.mem_filter.mp (Finset.mem_filter.mp htest).1).1
          have htest' := profileScheduledTests_length_bounds hq heN hlist
          exact Finset.mem_image.mpr ⟨test.anchor, Finset.mem_range.mpr (by omega), rfl⟩
        have himage := Finset.card_image_le (s := range (N + 1))
          (f := fun p ↦ ProfileChainState.fourier b e p v)
        exact (Finset.card_le_card hsubset).trans
          (by simpa only [Finset.card_range] using himage)
      · simp only [profileLongChildStates, hlarge, ite_false]
        have hcard := Finset.card_union_le
          ({.fourier b e (profileNearStart A q N δ b e a v) v} : Finset ProfileChainState)
          ((Ioo a (min (v + 1) (profileNearStart A q N δ b e a v + 12))).image
            (fun n ↦ ProfileChainState.discrepancy n v))
        have himage := Finset.card_image_le
          (s := Ioo a (min (v + 1) (profileNearStart A q N δ b e a v + 12)))
          (f := fun n ↦ ProfileChainState.discrepancy n v)
        have hmin := min_le_left (v + 1) (profileNearStart A q N δ b e a v + 12)
        simp only [Finset.card_singleton, Nat.card_Ioo] at hcard himage
        omega
  · simp only [profileChildStates, hlong, ite_false, Finset.card_empty]
    omega

/-- The actual enumeration satisfies the manuscript's stated branch cap. -/
theorem profileChildStates_card_le_source_bound {A : ℕ → ℝ} {q N δ : ℕ} (hq : 0 < q)
    {s : ProfileChainState} (hs : s.Valid N δ) :
    (profileChildStates A q N δ s).card ≤ N + 13 :=
  (profileChildStates_card_le hq hs).trans (by omega)

/-- The actual interval length strictly decreases on every transition. -/
theorem ProfileChainMove.width_decreases {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδpos : 0 < δ) (hδq : δ ≤ q) {s u : ProfileChainState}
    (hs : s.Valid N δ) (move : ProfileChainMove A q N δ s u) :
    u.finish - u.start < s.finish - s.start := by
  have hnested := move.nested_valid hq hδq hs
  cases move with
  | linearize a t hlong hright =>
    have hp := profileSplitPoint_bounds (A := A) hq hs.2 hlong
    change profileSplitPoint A q N a t - a < t - a
    omega
  | lowFrequency a t hlong hleft =>
    change t - δ - a < t - a
    omega
  | highFrequency a t v hlong hleft hvlo hvhi =>
    have hp := profileSplitPoint_bounds (A := A) hq hs.2 hlong
    change v - profileSplitPoint A q N a t < t - a
    omega
  | refine b e a v hlong test htest hlargest hlarge =>
    have hanchor := (Finset.mem_filter.mp htest).2
    change v - test.anchor < v - a
    omega
  | near b e a v hlong hsmall =>
    change v - (v - 2 * max (profileLongestTestLength A q N b e a) δ) < v - a
    omega
  | far b e a v n hlong hsmall hnlo hnhi hnv =>
    change v - n < v - a
    omega

/-- Recursive unfolding over the actual finite children terminates by interval length. -/
theorem profileChildStates_wellFounded {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδpos : 0 < δ) (hδq : δ ≤ q) :
    WellFounded (fun u s : ProfileChainState ↦
      u ∈ profileChildStates A q N δ s ∧ s.Valid N δ) := by
  refine Subrelation.wf ?_ (measure (fun s : ProfileChainState ↦ s.finish - s.start)).wf
  intro u s hrel
  obtain ⟨hu, hs⟩ := hrel
  obtain ⟨move⟩ := profileChildStates_move hu
  exact move.width_decreases hq hδpos hδq hs

end FalconerThetaGauge
