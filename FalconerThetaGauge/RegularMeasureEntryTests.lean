/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryScheduleGains

/-!
# Actual tube and projection tests contributed by one interval

Each concrete test records its kind, anchor and other endpoint. The origin
contains its symmetric length interval and contributes every shorter tube
test with the same anchor.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The two test types in the manuscript. -/
inductive ProfileTestKind
  | tube
  | projection
  deriving DecidableEq

instance : Fintype ProfileTestKind where
  elems := {.tube, .projection}
  complete := by intro k; cases k <;> simp

/-- A concrete finite-depth test with its anchor and other endpoint. -/
structure ProfileScheduleTest where
  kind : ProfileTestKind
  anchor : ℕ
  endpoint : ℕ
  deriving DecidableEq

/-- The length of a tube `[g,p]` or projection `[p,u]` test. -/
def ProfileScheduleTest.length (test : ProfileScheduleTest) : ℕ :=
  match test.kind with
  | .tube => test.anchor - test.endpoint
  | .projection => test.endpoint - test.anchor

/-- The concrete tube tests and possible projection test contributed by one split. -/
def profileTestsAtSplit (a p t : ℕ) : Finset ProfileScheduleTest :=
  ((Finset.Ico (p - min (p - a) (t - p)) p).image
    (fun g ↦ (⟨.tube, p, g⟩ : ProfileScheduleTest))) ∪
      if a + t < 2 * p then {⟨.projection, p, t⟩} else ∅

/-- The tests actually contributed by an interval, using its constructed split point. -/
def profileContributedTests (A : ℕ → ℝ) (q N a t : ℕ) : Finset ProfileScheduleTest :=
  profileTestsAtSplit a (profileSplitPoint A q N a t) t

/-- Every contributed test has its symmetric length interval in its origin, and
the origin contributes all tube tests no longer than it. -/
theorem profileTestsAtSplit_spec {a p t : ℕ} (hap : a < p) (hpt : p < t)
    {test : ProfileScheduleTest} (htest : test ∈ profileTestsAtSplit a p t) :
    test.anchor = p ∧ 0 < test.length ∧ test.length ≤ test.anchor ∧
      a ≤ test.anchor - test.length ∧
      test.anchor + test.length ≤ t ∧ test.endpoint ≤ t ∧
      ∀ g, test.anchor - test.length ≤ g → g < test.anchor →
        (⟨.tube, test.anchor, g⟩ : ProfileScheduleTest) ∈ profileTestsAtSplit a p t := by
  rcases Finset.mem_union.mp htest with htube | hprojection
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp htube
    obtain ⟨hglo, hgp⟩ := Finset.mem_Ico.mp hg
    change p - min (p - a) (t - p) ≤ g at hglo
    have hlen : p - g ≤ min (p - a) (t - p) := by omega
    have hleft := min_le_left (p - a) (t - p)
    have hright := min_le_right (p - a) (t - p)
    change p = p ∧ 0 < p - g ∧ p - g ≤ p ∧ a ≤ p - (p - g) ∧
      p + (p - g) ≤ t ∧ g ≤ t ∧ _
    refine ⟨rfl, by omega, by omega, by omega, by omega, by omega, ?_⟩
    intro g' hg'lo hg'p
    change p - (p - g) ≤ g' at hg'lo
    change g' < p at hg'p
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨g', Finset.mem_Ico.mpr ⟨by omega, hg'p⟩, rfl⟩
  · by_cases hr : a + t < 2 * p
    · have heq : test = ⟨.projection, p, t⟩ := by
        simpa only [hr, ite_true, Finset.mem_singleton] using hprojection
      subst test
      have hell : min (p - a) (t - p) = t - p := min_eq_right (by omega)
      change p = p ∧ 0 < t - p ∧ t - p ≤ p ∧ a ≤ p - (t - p) ∧
        p + (t - p) ≤ t ∧ t ≤ t ∧ _
      refine ⟨rfl, by omega, by omega, by omega, by omega, le_refl t, ?_⟩
      intro g hglo hgp
      change p - (t - p) ≤ g at hglo
      change g < p at hgp
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨g, Finset.mem_Ico.mpr ⟨by simpa only [hell] using hglo, hgp⟩, rfl⟩
    · simp only [hr, ite_false, Finset.notMem_empty] at hprojection

/-- The concrete tests of an actual long interval have the source's origin properties. -/
theorem profileContributedTests_spec {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    {test : ProfileScheduleTest} (htest : test ∈ profileContributedTests A q N a t) :
    test.anchor = profileSplitPoint A q N a t ∧ 0 < test.length ∧ test.length ≤ test.anchor ∧
      a ≤ test.anchor - test.length ∧ test.anchor + test.length ≤ t ∧ test.endpoint ≤ t ∧
      ∀ g, test.anchor - test.length ≤ g → g < test.anchor →
        (⟨.tube, test.anchor, g⟩ : ProfileScheduleTest) ∈ profileContributedTests A q N a t := by
  have hp := profileSplitPoint_bounds (A := A) hq ht hlong
  exact profileTestsAtSplit_spec (by omega) (by omega) htest

end FalconerThetaGauge
