module

public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwoFacts

/-! # Genuine longest-test origins supply the refinement tube and source geometry -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

theorem profileRemainingTests_refinement_tube {A : ℕ → ℝ} {q N b e a : ℕ}
    (hq : 0 < q) (he : e ≤ N) {test : ProfileScheduleTest}
    (htest : test ∈ profileRemainingTests A q N b e a) :
    (⟨.tube, test.anchor, max a (test.anchor - test.length)⟩ : ProfileScheduleTest) ∈
      profileRemainingTests A q N b e a := by
  obtain ⟨hlist, ha⟩ := mem_filter.mp htest
  have hb := profileScheduledTests_length_bounds hq he hlist
  apply mem_filter.mpr
  refine ⟨profileScheduledTests_origin_tubes hq he hlist (le_max_right _ _) ?_, ha⟩
  omega

/-- The anchor and the actual shorter tube have all three orthogonality margins. -/
theorem profileRemainingTests_refinement_geometry {A : ℕ → ℝ} {q N δ b e a v : ℕ}
    (hq : 0 < q) (hδq : δ ≤ q) (hs : (ProfileChainState.fourier b e a v).Valid N δ)
    (hlong : 100 * q < v - a) {test : ProfileScheduleTest}
    (htest : test ∈ profileRemainingTests A q N b e a) (hlarge : v - a ≤ 2 * test.length) :
    a ≤ max a (test.anchor - test.length) ∧
      max a (test.anchor - test.length) ≤ test.anchor ∧ test.anchor ≤ v ∧
      max a (test.anchor - test.length) - a ≤ δ ∧
      10 * δ + test.anchor ≤ v ∧
      test.anchor - a ≤ v - test.anchor + 2 * δ ∧
      test.length ≤ v - test.anchor + 2 * δ := by
  obtain ⟨_, _, _, he, hev⟩ := hs
  obtain ⟨hlist, ha⟩ := mem_filter.mp htest
  have hb := profileScheduledTests_length_bounds hq he hlist
  omega

theorem profileRemainingTests_length_le_longest {A : ℕ → ℝ} {q N b e a : ℕ}
    {test : ProfileScheduleTest} (htest : test ∈ profileRemainingTests A q N b e a) :
    test.length ≤ profileLongestTestLength A q N b e a := Finset.le_sup htest

theorem profileRemainingTests_refinement_real_geometry {A : ℕ → ℝ}
    {q N δ b e a v : ℕ} (hq : 0 < q) (hδq : δ ≤ q)
    (hs : (ProfileChainState.fourier b e a v).Valid N δ) (hlong : 100 * q < v - a)
    {test : ProfileScheduleTest} (htest : test ∈ profileRemainingTests A q N b e a)
    (hlarge : v - a ≤ 2 * test.length) {E : ℝ} (hE : E = (δ : ℝ)) :
    a ≤ max a (test.anchor - test.length) ∧
      max a (test.anchor - test.length) ≤ test.anchor ∧ test.anchor ≤ v ∧
      ((max a (test.anchor - test.length) : ℕ) : ℝ) - a ≤ E ∧
      10 * E ≤ (v : ℝ) - test.anchor ∧
      (test.anchor : ℝ) - a ≤ (v : ℝ) - test.anchor + 2 * E ∧
      (test.length : ℝ) ≤ (v : ℝ) - test.anchor + 2 * E := by
  have hg := profileRemainingTests_refinement_geometry hq hδq hs hlong htest hlarge
  have hanc : max a (test.anchor - test.length) ≤ a + δ := by omega
  have hgap : test.anchor + test.anchor ≤ a + v + 2 * δ := by omega
  have hlen : test.length + test.anchor ≤ v + 2 * δ := by omega
  have hanc' : ((max a (test.anchor - test.length) : ℕ) : ℝ) ≤ a + δ := by exact_mod_cast hanc
  have hwidth' : 10 * (δ : ℝ) + test.anchor ≤ v := by exact_mod_cast hg.2.2.2.2.1
  have hgap' : (test.anchor : ℝ) + test.anchor ≤ a + v + 2 * δ := by exact_mod_cast hgap
  have hlen' : (test.length : ℝ) + test.anchor ≤ v + 2 * δ := by exact_mod_cast hlen
  refine ⟨hg.1, hg.2.1, hg.2.2.1, ?_, ?_, ?_, ?_⟩ <;> rw [hE] <;> linarith

theorem profileHeight_refinement_le_parent {A : ℕ → ℝ} {a g p : ℕ}
    (hag : a ≤ g) (hgp : g ≤ p) : profileHeight A p g p ≤ profileHeight A p a p := by
  unfold profileHeight
  exact sub_le_sub_left (profileMinimum_mono hag hgp (le_refl p)) (A p)


end FalconerThetaGauge
