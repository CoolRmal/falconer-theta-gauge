/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryIntervals

/-!
# The actual discrete entry depth

The entry depth is the largest depth up to `N` at which the actual profile is
at most `β`. Its existence, maximality and one-generation boundary bound are
proved from the finite construction.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The actual depths at which the profile has not yet crossed the entry threshold. -/
def profileEntryCandidates (A : ℕ → ℝ) (β : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n ↦ A n ≤ β)

/-- The maximal entry depth `max{n≤N : A(n)≤β}`, with value zero for an empty set. -/
def profileEntryDepth (A : ℕ → ℝ) (β : ℝ) (N : ℕ) : ℕ :=
  (profileEntryCandidates A β N).sup id

theorem profileEntryCandidates_nonempty {A : ℕ → ℝ} {β : ℝ} (N : ℕ) (hzero : A 0 ≤ β) :
    (profileEntryCandidates A β N).Nonempty :=
  ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos N), hzero⟩⟩

theorem profileEntryDepth_mem {A : ℕ → ℝ} {β : ℝ} (N : ℕ) (hzero : A 0 ≤ β) :
    profileEntryDepth A β N ≤ N ∧ A (profileEntryDepth A β N) ≤ β := by
  have hmem : profileEntryDepth A β N ∈ profileEntryCandidates A β N := by
    have h := Finset.sup_mem_of_nonempty (f := id) (profileEntryCandidates_nonempty N hzero)
    simpa only [profileEntryDepth, Set.image_id, Finset.mem_coe] using h
  obtain ⟨hn, hA⟩ := Finset.mem_filter.mp hmem
  exact ⟨by have := Finset.mem_range.mp hn; omega, hA⟩

theorem le_profileEntryDepth {A : ℕ → ℝ} {β : ℝ} {N n : ℕ}
    (hn : n ≤ N) (hA : A n ≤ β) : n ≤ profileEntryDepth A β N :=
  Finset.le_sup (s := profileEntryCandidates A β N) (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hA⟩)

theorem profileEntryDepth_above {A : ℕ → ℝ} {β : ℝ} {N n : ℕ}
    (hc : profileEntryDepth A β N < n) (hn : n ≤ N) : β < A n := by
  by_contra h
  have hmax := le_profileEntryDepth hn (le_of_not_gt h)
  omega

/-- The upper profile barrier ensures entry is no earlier than `floor(βN)`. -/
theorem floor_gain_mul_le_profileEntryDepth {A : ℕ → ℝ} {β : ℝ} {N : ℕ}
    (hN : 0 < N) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hupper : ∀ n ≤ N, A n ≤ (n : ℝ) / N) :
    ⌊β * N⌋₊ ≤ profileEntryDepth A β N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor : (⌊β * N⌋₊ : ℝ) ≤ β * N := Nat.floor_le (by positivity)
  have hleN : ⌊β * N⌋₊ ≤ N := by
    exact_mod_cast hfloor.trans (by nlinarith : β * N ≤ (N : ℝ))
  exact le_profileEntryDepth hleN ((hupper _ hleN).trans ((div_le_iff₀ hN').mpr hfloor))

/-- A quarter-scale lower barrier puts the entry strictly before `N/4`. -/
theorem profileEntryDepth_lt_quarter {A : ℕ → ℝ} {β : ℝ} {N : ℕ}
    (hzero : A 0 ≤ β)
    (hlower : ∀ n ≤ N, (N : ℝ) / 4 ≤ n → β < A n) :
    (profileEntryDepth A β N : ℝ) < (N : ℝ) / 4 := by
  by_contra h
  have hc := profileEntryDepth_mem N hzero
  exact (hlower _ hc.1 (le_of_not_gt h)).not_ge hc.2

/-- The boundary depth itself remains strictly above `β−1/N`. -/
theorem profileEntryDepth_boundary_lower {A : ℕ → ℝ} {β : ℝ} {N : ℕ}
    (hc : profileEntryDepth A β N < N)
    (hstep : ∀ n < N, |A (n + 1) - A n| ≤ 1 / (N : ℝ)) :
    β - 1 / (N : ℝ) < A (profileEntryDepth A β N) := by
  have habove := profileEntryDepth_above (Nat.lt_succ_self _) (by omega :
    profileEntryDepth A β N + 1 ≤ N)
  have hbound := (le_abs_self _).trans (hstep _ hc)
  linarith

theorem profileEntryDepth_interval_lower {A : ℕ → ℝ} {β : ℝ} {N : ℕ}
    (hN : 0 < N) (hc : profileEntryDepth A β N < N)
    (hstep : ∀ n < N, |A (n + 1) - A n| ≤ 1 / (N : ℝ)) {n : ℕ}
    (hnc : profileEntryDepth A β N ≤ n) (hnN : n ≤ N) :
    β - 1 / (N : ℝ) < A n := by
  by_cases hn : n = profileEntryDepth A β N
  · rw [hn]
    exact profileEntryDepth_boundary_lower hc hstep
  · have hβ := profileEntryDepth_above (by omega : profileEntryDepth A β N < n) hnN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hpositive : 0 < 1 / (N : ℝ) := by positivity
    linarith

/-- The budget of the post-entry interval has the gain claimed in Lemma 9.2(ii). -/
theorem profileEntryDepth_budget_lower {A : ℕ → ℝ} {β : ℝ} {N q : ℕ}
    (hN : 0 < N)
    (hmargin : profileEntryDepth A β N + 10 * q ≤ N)
    (hc : profileEntryDepth A β N < N)
    (hstep : ∀ n < N, |A (n + 1) - A n| ≤ 1 / (N : ℝ)) :
    2 * β - 2 / (N : ℝ) ≤ profileBudget A q (profileEntryDepth A β N) N := by
  have hlo₁ : β - 1 / (N : ℝ) ≤
      profileMinimum A (profileEntryDepth A β N) (N - 10 * q) :=
    le_profileMinimum (by omega) (fun n hn _ ↦
      (profileEntryDepth_interval_lower hN hc hstep hn (by omega)).le)
  have hlo₂ : β - 1 / (N : ℝ) ≤
      profileMinimum A (profileEntryDepth A β N + 10 * q) N :=
    le_profileMinimum hmargin (fun n hn hnN ↦
      (profileEntryDepth_interval_lower hN hc hstep (by omega) hnN).le)
  unfold profileBudget
  rw [show (2 : ℝ) / N = 2 * (1 / (N : ℝ)) by ring]
  linarith

/-- The entry height costs at most the original threshold plus the lower profile loss. -/
theorem profileEntryDepth_height_le {A : ℕ → ℝ} {β κ : ℝ} {N : ℕ}
    (hzero : A 0 ≤ β) (hlower : ∀ n ≤ N, -κ ≤ A n) :
    profileHeight A (profileEntryDepth A β N) 0 (profileEntryDepth A β N) ≤ β + κ := by
  have hc := profileEntryDepth_mem N hzero
  have h := profileHeight_le_of_bounds (by omega : 0 ≤ profileEntryDepth A β N)
    (fun n _ hn ↦ hlower n (hn.trans hc.1)) hc.2
  linarith

end FalconerThetaGauge
