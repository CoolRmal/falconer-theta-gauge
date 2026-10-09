/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryTests

/-!
# Actual scheduled test lists and their origins

The list of an interval is the actual finite union over all its long
subintervals. Its tests retain real origins, the lists increase with interval
inclusion, and their exact cardinality is bounded by `N²` at the parameters
of the manuscript.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The actual long subintervals contributing tests to `[a,t]`. -/
def profileScheduleOrigins (q a t : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc a t).product (Finset.Icc a t)).filter (fun r ↦ 100 * q < r.2 - r.1)

/-- The actual list `T([a,t])`, as a finite set of concrete tube and projection tests. -/
def profileScheduledTests (A : ℕ → ℝ) (q N a t : ℕ) : Finset ProfileScheduleTest :=
  (profileScheduleOrigins q a t).biUnion (fun r ↦ profileContributedTests A q N r.1 r.2)

theorem mem_profileScheduleOrigins_iff {q a t a' t' : ℕ} :
    (a', t') ∈ profileScheduleOrigins q a t ↔
      a ≤ a' ∧ a' ≤ t ∧ a ≤ t' ∧ t' ≤ t ∧ 100 * q < t' - a' := by
  simp only [profileScheduleOrigins, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Actual test lists increase under inclusion of their intervals. -/
theorem profileScheduledTests_mono (A : ℕ → ℝ) (q N : ℕ) {a t c d : ℕ}
    (hac : a ≤ c) (hdt : d ≤ t) :
    profileScheduledTests A q N c d ⊆ profileScheduledTests A q N a t := by
  intro test htest
  obtain ⟨⟨a', t'⟩, horigin, htest'⟩ := Finset.mem_biUnion.mp htest
  obtain ⟨hc₁, hc₂, ht₁, ht₂, hlong⟩ := mem_profileScheduleOrigins_iff.mp horigin
  exact Finset.mem_biUnion.mpr ⟨(a', t'), mem_profileScheduleOrigins_iff.mpr
    ⟨hac.trans hc₁, hc₂.trans hdt, hac.trans ht₁, ht₂.trans hdt, hlong⟩, htest'⟩

/-- Each scheduled test has an actual long origin with all the properties of Lemma 8.3(c). -/
theorem profileScheduledTests_origin {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profileScheduledTests A q N a t) :
    ∃ a' t', a ≤ a' ∧ t' ≤ t ∧ 100 * q < t' - a' ∧
      test.anchor = profileSplitPoint A q N a' t' ∧ 0 < test.length ∧
      test.length ≤ test.anchor ∧ a' ≤ test.anchor - test.length ∧
      test.anchor + test.length ≤ t' ∧ test.endpoint ≤ t' ∧
      ∀ g, test.anchor - test.length ≤ g → g < test.anchor →
        (⟨.tube, test.anchor, g⟩ : ProfileScheduleTest) ∈ profileContributedTests A q N a' t' := by
  obtain ⟨⟨a', t'⟩, horigin, htest'⟩ := Finset.mem_biUnion.mp htest
  obtain ⟨ha₁, _, _, ht₂, hlong⟩ := mem_profileScheduleOrigins_iff.mp horigin
  have hs := profileContributedTests_spec hq (ht₂.trans ht) hlong htest'
  exact ⟨a', t', ha₁, ht₂, hlong, hs⟩

/-- Every actual scheduled anchor is one of the finitely many marked depths. -/
theorem profileScheduledTests_anchor_mem {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profileScheduledTests A q N a t) : test.anchor ∈ profileMarkedDepths A q N := by
  obtain ⟨a', t', _, ht', hlong, hanchor, _⟩ := profileScheduledTests_origin hq ht htest
  rw [hanchor]
  exact profileSplitPoint_mem_marked hq (ht'.trans ht) hlong

/-- The origin supplies every shorter tube test to the full parent list. -/
theorem profileScheduledTests_origin_tubes {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profileScheduledTests A q N a t) {g : ℕ}
    (hglo : test.anchor - test.length ≤ g) (hghi : g < test.anchor) :
    (⟨.tube, test.anchor, g⟩ : ProfileScheduleTest) ∈ profileScheduledTests A q N a t := by
  obtain ⟨⟨a', t'⟩, horigin, htest'⟩ := Finset.mem_biUnion.mp htest
  obtain ⟨_, _, _, ht', hlong⟩ := mem_profileScheduleOrigins_iff.mp horigin
  have hs := profileContributedTests_spec hq (ht'.trans ht) hlong htest'
  exact Finset.mem_biUnion.mpr ⟨(a', t'), horigin, hs.2.2.2.2.2.2 g hglo hghi⟩

/-- The symmetric length interval of every test lies inside its parent's interval. -/
theorem profileScheduledTests_length_bounds {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profileScheduledTests A q N a t) :
    0 < test.length ∧ test.length ≤ test.anchor ∧
      a ≤ test.anchor - test.length ∧ test.anchor + test.length ≤ t ∧
      2 * test.length ≤ t - a ∧ test.endpoint ≤ N := by
  obtain ⟨a', t', ha', ht', _, _, hlenpos, hlenanchor, hleft, hright, hendpoint, _⟩ :=
    profileScheduledTests_origin hq ht htest
  exact ⟨hlenpos, hlenanchor, ha'.trans hleft, hright.trans ht', by omega,
    hendpoint.trans (ht'.trans ht)⟩

/-- The actual finite range of test records with a marked anchor and depth endpoint. -/
def profileAllTestSlots (A : ℕ → ℝ) (q N : ℕ) : Finset ProfileScheduleTest :=
  ((Finset.univ : Finset ProfileTestKind).product
    ((profileMarkedDepths A q N).product (Finset.range (N + 1)))).image
      (fun r ↦ ⟨r.1, r.2.1, r.2.2⟩)

theorem profileScheduledTests_subset_slots {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) :
    profileScheduledTests A q N a t ⊆ profileAllTestSlots A q N := by
  intro test htest
  apply Finset.mem_image.mpr
  refine ⟨(test.kind, test.anchor, test.endpoint), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
    ⟨profileScheduledTests_anchor_mem hq ht htest, Finset.mem_range.mpr
      (Nat.lt_succ_of_le (profileScheduledTests_length_bounds hq ht htest).2.2.2.2.2)⟩⟩

/-- The exact finite test count is at most twice the number of anchors times the depth count. -/
theorem profileScheduledTests_card_le {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) :
    (profileScheduledTests A q N a t).card ≤ 2 * (profileMarkedDepths A q N).card * (N + 1) := by
  have hkind : Fintype.card ProfileTestKind = 2 := by decide
  calc
    _ ≤ (profileAllTestSlots A q N).card :=
      Finset.card_le_card (profileScheduledTests_subset_slots hq ht)
    _ ≤ ((Finset.univ : Finset ProfileTestKind).product
        ((profileMarkedDepths A q N).product (Finset.range (N + 1)))).card := Finset.card_image_le
    _ = _ := by
      simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, hkind,
        Finset.card_range]
      ring

/-- At the literal rounded parameters, every scheduled list has at most `N²` tests. -/
theorem profileScheduledTests_card_le_scale_sq (A : ℕ → ℝ) {θ : ℝ} {N a t : ℕ}
    (hpar : ParameterFacts θ N) (ht : t ≤ N) :
    (profileScheduledTests A (blockCount θ N) N a t).card ≤ N ^ 2 := by
  rcases hpar with ⟨hN₄, _, _, _, _, _, _, _, _, _, _, hbudget⟩
  have hN : 0 < N := by omega
  have hmarks := profileMarkedDepths_card_le_inverse_block A θ hN
  have hcount : ((profileScheduledTests A (blockCount θ N) N a t).card : ℝ) ≤
      2 * ((profileMarkedDepths A (blockCount θ N) N).card : ℝ) * (N + 1) := by
    exact_mod_cast profileScheduledTests_card_le (A := A) (blockCount_pos θ hN) ht
  have hreal : ((profileScheduledTests A (blockCount θ N) N a t).card : ℝ) ≤ (N : ℝ) ^ 2 :=
    hcount.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmarks (by norm_num))
      (by positivity)).trans hbudget)
  exact_mod_cast hreal

end FalconerThetaGauge
