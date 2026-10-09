module

public import FalconerThetaGauge.ScheduledStateEnergiesReached
public import FalconerThetaGauge.MaskedDistanceEnergyOrderedLists

/-! # The actual left split supplies every orthogonality hypothesis in Move 2 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

theorem profileRemainingTests_at_base (A : ℕ → ℝ) {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) :
    profileRemainingTests A q N a t a = profileScheduledTests A q N a t := by
  apply Finset.filter_eq_self.mpr
  intro test htest
  exact profileScheduledTests_anchor_strict hq ht htest

/-- A genuine left split contributes the whole interval's tube to the actual scheduled list. -/
theorem profileScheduledTests_left_split_tube {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    (hleft : 2 * profileSplitPoint A q N a t ≤ a + t) :
    (⟨.tube, profileSplitPoint A q N a t, a⟩ : ProfileScheduleTest) ∈
      profileScheduledTests A q N a t := by
  have hp := profileSplitPoint_bounds (A := A) hq ht hlong
  apply Finset.mem_biUnion.mpr
  refine ⟨(a, t), mem_profileScheduleOrigins_iff.mpr
    ⟨le_refl a, by omega, by omega, le_refl t, hlong⟩, ?_⟩
  unfold profileContributedTests profileTestsAtSplit
  dsimp only
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_Ico.mpr ⟨?_, by omega⟩, rfl⟩
  have hmin : min (profileSplitPoint A q N a t - a)
      (t - profileSplitPoint A q N a t) = profileSplitPoint A q N a t - a := by
    exact min_eq_left (by omega)
  rw [hmin]
  omega

/-- The literal rounded high shell and left split give all three source width inequalities. -/
theorem profileSplitPoint_left_shell_geometry {A : ℕ → ℝ} {q N a t δ v : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a) (hδ : δ ≤ q)
    (hleft : 2 * profileSplitPoint A q N a t ≤ a + t) (hvlo : t - δ < v) :
    a ≤ profileSplitPoint A q N a t ∧ profileSplitPoint A q N a t ≤ v ∧
      10 * δ + profileSplitPoint A q N a t ≤ v ∧
      profileSplitPoint A q N a t - a ≤ v - profileSplitPoint A q N a t + 2 * δ ∧
      (t - a) / 2 ≤ v - profileSplitPoint A q N a t + 2 * δ := by
  have hp := profileSplitPoint_bounds (A := A) hq ht hlong
  omega

theorem directionalLevelWidth_ge_one {levels i : ℕ} (hlevels : 0 < levels)
    (hi : i ≤ levels) : 1 ≤ directionalLevelWidth levels i := by
  unfold directionalLevelWidth
  have hl : (0 : ℝ) < levels := by exact_mod_cast hlevels
  have hii : (i : ℝ) ≤ levels := by exact_mod_cast hi
  have hdiv : (i : ℝ) / levels ≤ 1 := (div_le_one hl).mpr hii
  linarith

end FalconerThetaGauge
