/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryTestLists

/-!
# Concrete combinatorial states of the energy induction

Fourier states use the actual scheduled list of their base interval, retaining
exactly the tests whose anchors have not yet been reached. The six transition
constructors are the child types of Table 1 in the manuscript.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The actual tests still present at start depth `a` in a Fourier state. -/
def profileRemainingTests (A : ℕ → ℝ) (q N b e a : ℕ) : Finset ProfileScheduleTest :=
  (profileScheduledTests A q N b e).filter (fun test ↦ a < test.anchor)

/-- The length of the longest remaining test, with value zero for the empty list. -/
def profileLongestTestLength (A : ℕ → ℝ) (q N b e a : ℕ) : ℕ :=
  (profileRemainingTests A q N b e a).sup ProfileScheduleTest.length

theorem profileRemainingTests_mono (A : ℕ → ℝ) (q N b e : ℕ) {a c : ℕ}
    (hac : a ≤ c) :
    profileRemainingTests A q N b e c ⊆ profileRemainingTests A q N b e a := by
  intro test htest
  obtain ⟨hlist, hanchor⟩ := Finset.mem_filter.mp htest
  exact Finset.mem_filter.mpr ⟨hlist, hac.trans_lt hanchor⟩

theorem profileLongestTestLength_mono (A : ℕ → ℝ) (q N b e : ℕ) {a c : ℕ}
    (hac : a ≤ c) :
    profileLongestTestLength A q N b e c ≤ profileLongestTestLength A q N b e a :=
  Finset.sup_mono (profileRemainingTests_mono A q N b e hac)

theorem profileLongestTestLength_attained {A : ℕ → ℝ} {q N b e a : ℕ}
    (hL : 0 < profileLongestTestLength A q N b e a) :
    ∃ test ∈ profileRemainingTests A q N b e a,
      test.length = profileLongestTestLength A q N b e a := by
  have hne : (profileRemainingTests A q N b e a).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [profileLongestTestLength, hempty, Finset.sup_empty] at hL
    change 0 < (0 : ℕ) at hL
    omega
  obtain ⟨test, htest, heq⟩ :=
    Finset.exists_mem_eq_sup (profileRemainingTests A q N b e a) hne
      ProfileScheduleTest.length
  exact ⟨test, htest, heq.symm⟩

/-- A discrepancy state, or a Fourier state with the actual base interval. -/
inductive ProfileChainState
  | discrepancy (start finish : ℕ)
  | fourier (baseStart baseFinish start finish : ℕ)
  deriving DecidableEq

def ProfileChainState.start : ProfileChainState → ℕ
  | .discrepancy a _ => a
  | .fourier _ _ a _ => a

def ProfileChainState.finish : ProfileChainState → ℕ
  | .discrepancy _ t => t
  | .fourier _ _ _ v => v

def ProfileChainState.isFourier : ProfileChainState → Bool
  | .discrepancy _ _ => false
  | .fourier _ _ _ _ => true

/-- The actual interval and base requirements of Definition 8.4. -/
def ProfileChainState.Valid (N δ : ℕ) : ProfileChainState → Prop
  | .discrepancy a t => a ≤ t ∧ t ≤ N
  | .fourier b e a v => b ≤ a ∧ a ≤ v ∧ v ≤ e ∧ e ≤ N ∧ e ≤ v + δ

/-- The six child types of the four moves, with their concrete intervals and masks. -/
inductive ProfileChainMove (A : ℕ → ℝ) (q N δ : ℕ) :
    ProfileChainState → ProfileChainState → Type
  | linearize (a t : ℕ) (hlong : 100 * q < t - a)
      (hright : a + t < 2 * profileSplitPoint A q N a t) :
      ProfileChainMove A q N δ (.discrepancy a t)
        (.discrepancy a (profileSplitPoint A q N a t))
  | lowFrequency (a t : ℕ) (hlong : 100 * q < t - a)
      (hleft : 2 * profileSplitPoint A q N a t ≤ a + t) :
      ProfileChainMove A q N δ (.discrepancy a t) (.discrepancy a (t - δ))
  | highFrequency (a t v : ℕ) (hlong : 100 * q < t - a)
      (hleft : 2 * profileSplitPoint A q N a t ≤ a + t)
      (hvlo : t - δ < v) (hvhi : v ≤ t) :
      ProfileChainMove A q N δ (.discrepancy a t)
        (.fourier a t (profileSplitPoint A q N a t) v)
  | refine (b e a v : ℕ) (hlong : 100 * q < v - a) (test : ProfileScheduleTest)
      (htest : test ∈ profileRemainingTests A q N b e a)
      (hlargest : test.length = profileLongestTestLength A q N b e a)
      (hlarge : v - a ≤ 2 * test.length) :
      ProfileChainMove A q N δ (.fourier b e a v) (.fourier b e test.anchor v)
  | near (b e a v : ℕ) (hlong : 100 * q < v - a)
      (hsmall : 2 * profileLongestTestLength A q N b e a < v - a) :
      ProfileChainMove A q N δ (.fourier b e a v)
        (.fourier b e (v - 2 * max (profileLongestTestLength A q N b e a) δ) v)
  | far (b e a v n : ℕ) (hlong : 100 * q < v - a)
      (hsmall : 2 * profileLongestTestLength A q N b e a < v - a)
      (hnlo : a < n)
      (hnhi : n < v - 2 * max (profileLongestTestLength A q N b e a) δ + 12)
      (hnv : n ≤ v) :
      ProfileChainMove A q N δ (.fourier b e a v) (.discrepancy n v)

/-- Numerical names distinguish the six child types, including both Fourier-side children. -/
def ProfileChainMove.tag {A : ℕ → ℝ} {q N δ : ℕ} {s u : ProfileChainState} :
    ProfileChainMove A q N δ s u → ℕ
  | .linearize .. => 0
  | .lowFrequency .. => 1
  | .highFrequency .. => 2
  | .refine .. => 3
  | .near .. => 4
  | .far .. => 5

/-- Every move starts from a long state. -/
theorem ProfileChainMove.long {A : ℕ → ℝ} {q N δ : ℕ} {s u : ProfileChainState}
    (move : ProfileChainMove A q N δ s u) : 100 * q < s.finish - s.start := by
  cases move <;> assumption

/-- Actual move intervals are nested, and their children satisfy the state requirements. -/
theorem ProfileChainMove.nested_valid {A : ℕ → ℝ} {q N δ : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) {s u : ProfileChainState}
    (hs : s.Valid N δ) (move : ProfileChainMove A q N δ s u) :
    s.start ≤ u.start ∧ u.finish ≤ s.finish ∧ u.Valid N δ := by
  cases move with
  | linearize a t hlong hright =>
    obtain ⟨hat, ht⟩ := hs
    have hp := profileSplitPoint_bounds (A := A) hq ht hlong
    change a ≤ a ∧ profileSplitPoint A q N a t ≤ t ∧ _
    exact ⟨le_refl a, by omega, by change a ≤ _ ∧ _ ≤ N; omega⟩
  | lowFrequency a t hlong hleft =>
    obtain ⟨hat, ht⟩ := hs
    change a ≤ a ∧ t - δ ≤ t ∧ a ≤ t - δ ∧ t - δ ≤ N
    omega
  | highFrequency a t v hlong hleft hvlo hvhi =>
    obtain ⟨hat, ht⟩ := hs
    have hp := profileSplitPoint_bounds (A := A) hq ht hlong
    change a ≤ profileSplitPoint A q N a t ∧ v ≤ t ∧
      a ≤ profileSplitPoint A q N a t ∧ profileSplitPoint A q N a t ≤ v ∧
      v ≤ t ∧ t ≤ N ∧ t ≤ v + δ
    omega
  | refine b e a v hlong test htest hlargest hlarge =>
    obtain ⟨hba, hav, hve, heN, hev⟩ := hs
    obtain ⟨hlist, hanchor⟩ := Finset.mem_filter.mp htest
    have htest' := profileScheduledTests_length_bounds hq heN hlist
    change a ≤ test.anchor ∧ v ≤ v ∧ b ≤ test.anchor ∧ test.anchor ≤ v ∧
      v ≤ e ∧ e ≤ N ∧ e ≤ v + δ
    omega
  | near b e a v hlong hsmall =>
    obtain ⟨hba, hav, hve, heN, hev⟩ := hs
    have hmax : 2 * max (profileLongestTestLength A q N b e a) δ < v - a := by
      omega
    change a ≤ v - 2 * max (profileLongestTestLength A q N b e a) δ ∧ v ≤ v ∧
      b ≤ v - 2 * max (profileLongestTestLength A q N b e a) δ ∧
      v - 2 * max (profileLongestTestLength A q N b e a) δ ≤ v ∧
      v ≤ e ∧ e ≤ N ∧ e ≤ v + δ
    omega
  | far b e a v n hlong hsmall hnlo hnhi hnv =>
    obtain ⟨hba, hav, hve, heN, hev⟩ := hs
    change a ≤ n ∧ v ≤ v ∧ n ≤ v ∧ v ≤ N
    omega

end FalconerThetaGauge
