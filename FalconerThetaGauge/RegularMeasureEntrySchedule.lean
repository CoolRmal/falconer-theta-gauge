/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryScheduleBlocks

/-!
# Actual inner intervals and marked split points

The split point minimizes the marked values among the full blocks inside
`[a+q,t-q]`. Their actual union is an interval, contains `[a+2q,t-2q]`, and
the profile on that union lies above the split value.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The actual blocks contained in the shrunken interval `[a+q,t-q]`. -/
def profileInnerBlocks (q N a t : ℕ) : Finset ℕ :=
  (Finset.range (N / q + 1)).filter
    (fun b ↦ a + q ≤ profileBlockStart q b ∧ profileBlockEnd q N b ≤ t - q)

/-- The actual union of the contained blocks, the inner interval `I([a,t])`. -/
def profileInnerDepths (q N a t : ℕ) : Finset ℕ :=
  (profileInnerBlocks q N a t).biUnion (profileDepthBlock q N)

/-- The actual marked candidates for the split point. -/
def profileSplitCandidates (A : ℕ → ℝ) (q N a t : ℕ) : Finset ℕ :=
  (profileInnerBlocks q N a t).image (profileMarkedDepth A q N)

/-- The fixed minimizing marked split point of the actual inner interval. -/
def profileSplitPoint (A : ℕ → ℝ) (q N a t : ℕ) : ℕ :=
  finiteProfileMinimizer A (profileSplitCandidates A q N a t)

theorem quotient_mem_profileInnerBlocks {q N a t n : ℕ} (hq : 0 < q)
    (ht : t ≤ N) (han : a + 2 * q ≤ n) (hnt : n ≤ t - 2 * q) :
    n / q ∈ profileInnerBlocks q N a t := by
  have hnN : n ≤ N := by omega
  have hb : n / q ≤ N / q := Nat.div_le_div_right hnN
  have hlo := Nat.div_mul_le_self n q
  have hhi := Nat.lt_mul_div_succ n hq
  rw [Nat.mul_comm q, Nat.add_mul, Nat.one_mul] at hhi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
  · unfold profileBlockStart
    omega
  · unfold profileBlockEnd
    rw [Nat.add_mul, Nat.one_mul]
    have hraw : n / q * q + q - 1 ≤ t - q := by omega
    exact (min_le_left _ _).trans hraw

/-- Every middle depth belongs to a full block inside the shrunken interval. -/
theorem mem_profileInnerDepths_of_middle {q N a t n : ℕ} (hq : 0 < q)
    (ht : t ≤ N) (han : a + 2 * q ≤ n) (hnt : n ≤ t - 2 * q) :
    n ∈ profileInnerDepths q N a t :=
  Finset.mem_biUnion.mpr ⟨n / q, quotient_mem_profileInnerBlocks hq ht han hnt,
    mem_profileDepthBlock_quotient hq (by omega)⟩

theorem profileInnerDepths_bounds {q N a t n : ℕ}
    (hn : n ∈ profileInnerDepths q N a t) : a + q ≤ n ∧ n ≤ t - q := by
  obtain ⟨b, hb, hnblock⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hb
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hnblock
  exact ⟨hlo.trans hnlo, hnhi.trans hhi⟩

/-- The union of the actual contained blocks is an interval of depths. -/
theorem profileInnerDepths_between {q N a t x y z : ℕ} (hq : 0 < q)
    (hx : x ∈ profileInnerDepths q N a t) (hz : z ∈ profileInnerDepths q N a t)
    (hxy : x ≤ y) (hyz : y ≤ z) : y ∈ profileInnerDepths q N a t := by
  obtain ⟨bx, hbx, hxblock⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨bz, hbz, hzblock⟩ := Finset.mem_biUnion.mp hz
  have hxdiv := div_eq_of_mem_profileDepthBlock hq hxblock
  have hzdiv := div_eq_of_mem_profileDepthBlock hq hzblock
  have hzN : z ≤ N := (Finset.mem_Icc.mp hzblock).2.trans (min_le_right _ _)
  have hyN : y ≤ N := hyz.trans hzN
  have hyindex : y / q ≤ N / q := Nat.div_le_div_right hyN
  have hxindex : bx ≤ y / q := by rw [← hxdiv]; exact Nat.div_le_div_right hxy
  have hzindex : y / q ≤ bz := by rw [← hzdiv]; exact Nat.div_le_div_right hyz
  have hstart : a + q ≤ profileBlockStart q (y / q) :=
    (Finset.mem_filter.mp hbx).2.1.trans (profileBlockStart_mono q hxindex)
  have hend : profileBlockEnd q N (y / q) ≤ t - q :=
    (profileBlockEnd_mono q N hzindex).trans (Finset.mem_filter.mp hbz).2.2
  apply Finset.mem_biUnion.mpr
  exact ⟨y / q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hstart, hend⟩,
    mem_profileDepthBlock_quotient hq hyN⟩

theorem profileInnerBlocks_nonempty {q N a t : ℕ} (hq : 0 < q) (ht : t ≤ N)
    (hlong : 100 * q < t - a) : (profileInnerBlocks q N a t).Nonempty :=
  ⟨(a + 2 * q) / q, quotient_mem_profileInnerBlocks hq ht (le_refl _) (by omega)⟩

theorem profileSplitCandidates_nonempty {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a) :
    (profileSplitCandidates A q N a t).Nonempty :=
  (profileInnerBlocks_nonempty hq ht hlong).image _

/-- The actual split is a marked depth from one of the actual contained blocks. -/
theorem profileSplitPoint_block {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a) :
    ∃ b ∈ profileInnerBlocks q N a t, profileSplitPoint A q N a t = profileMarkedDepth A q N b := by
  have hp := finiteProfileMinimizer_mem (A := A)
    (profileSplitCandidates_nonempty (A := A) hq ht hlong)
  obtain ⟨b, hb, hbp⟩ := Finset.mem_image.mp hp
  exact ⟨b, hb, hbp.symm⟩

theorem profileSplitPoint_mem_inner {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a) :
    profileSplitPoint A q N a t ∈ profileInnerDepths q N a t := by
  obtain ⟨b, hb, hp⟩ := profileSplitPoint_block hq ht hlong
  have hbindex : b ≤ N / q := by have := Finset.mem_range.mp (Finset.mem_filter.mp hb).1; omega
  rw [hp]
  exact Finset.mem_biUnion.mpr ⟨b, hb, (profileMarkedDepth_spec hq hbindex).1⟩

theorem profileSplitPoint_mem_marked {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a) :
    profileSplitPoint A q N a t ∈ profileMarkedDepths A q N := by
  obtain ⟨b, hb, hp⟩ := profileSplitPoint_block hq ht hlong
  rw [hp]
  apply profileMarkedDepth_mem_markedDepths
  have := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  omega

theorem profileSplitPoint_bounds {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a) :
    a + q ≤ profileSplitPoint A q N a t ∧ profileSplitPoint A q N a t ≤ t - q :=
  profileInnerDepths_bounds (profileSplitPoint_mem_inner hq ht hlong)

/-- The actual profile is at least the split value throughout the actual inner interval. -/
theorem profileSplitPoint_le_on_inner {A : ℕ → ℝ} {q N a t n : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    (hn : n ∈ profileInnerDepths q N a t) : A (profileSplitPoint A q N a t) ≤ A n := by
  obtain ⟨b, hb, hnblock⟩ := Finset.mem_biUnion.mp hn
  have hbindex : b ≤ N / q := by have := Finset.mem_range.mp (Finset.mem_filter.mp hb).1; omega
  exact (finiteProfileMinimizer_le (profileSplitCandidates_nonempty hq ht hlong)
    (Finset.mem_image_of_mem _ hb)).trans ((profileMarkedDepth_spec hq hbindex).2 n hnblock)

/-- The actual split value is a lower bound on the full middle depth interval. -/
theorem profileSplitPoint_le_on_middle {A : ℕ → ℝ} {q N a t n : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    (han : a + 2 * q ≤ n) (hnt : n ≤ t - 2 * q) : A (profileSplitPoint A q N a t) ≤ A n :=
  profileSplitPoint_le_on_inner hq ht hlong (mem_profileInnerDepths_of_middle hq ht han hnt)

/-- The actual minimum plateau extends from `a+2q` to the split, including an edge block. -/
theorem profileSplitPoint_le_on_left {A : ℕ → ℝ} {q N a t n : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    (han : a + 2 * q ≤ n) (hnp : n ≤ profileSplitPoint A q N a t) :
    A (profileSplitPoint A q N a t) ≤ A n :=
  profileSplitPoint_le_on_inner hq ht hlong (profileInnerDepths_between hq
    (mem_profileInnerDepths_of_middle hq ht (le_refl _) (by omega))
    (profileSplitPoint_mem_inner hq ht hlong) han hnp)

/-- The actual minimum plateau extends from the split to `t-2q`. -/
theorem profileSplitPoint_le_on_right {A : ℕ → ℝ} {q N a t n : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    (hpn : profileSplitPoint A q N a t ≤ n) (hnt : n ≤ t - 2 * q) :
    A (profileSplitPoint A q N a t) ≤ A n :=
  profileSplitPoint_le_on_inner hq ht hlong (profileInnerDepths_between hq
    (profileSplitPoint_mem_inner hq ht hlong)
    (mem_profileInnerDepths_of_middle hq ht (by omega) (le_refl _)) hpn hnt)

end FalconerThetaGauge
