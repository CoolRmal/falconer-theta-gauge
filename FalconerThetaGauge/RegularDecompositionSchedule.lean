/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularDecompositionFinite

/-!
# Forward sampled depths and the reversed bottom-up schedule

The exact sampled depths `nᵢ = min(iΔ,N)` are reversed to build types from the
terminal cells upward. Every generation lies in a sampled block, including the
possibly shorter final block.
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

/-- The manuscript's sampled generation `nᵢ = min(iΔ,N)`. -/
def regularDecompositionSampledDepth (ε : ℝ) (N i : ℕ) : ℕ :=
  min (i * regularDecompositionBlockLength ε N) N

/-- The height above terminal generation `N` in the reversed sampled schedule. -/
def regularDecompositionSampledHeight (ε : ℝ) (N j : ℕ) : ℕ :=
  N - regularDecompositionSampledDepth ε N (regularDecompositionBlockCount ε N - j)

theorem regularDecomposition_sampledDepth_zero (ε : ℝ) (N : ℕ) :
    regularDecompositionSampledDepth ε N 0 = 0 := by
  simp [regularDecompositionSampledDepth]

theorem regularDecomposition_sampledDepth_le (ε : ℝ) (N i : ℕ) :
    regularDecompositionSampledDepth ε N i ≤ N :=
  min_le_right _ _

theorem regularDecomposition_sampledDepth_monotone (ε : ℝ) (N : ℕ) :
    Monotone (regularDecompositionSampledDepth ε N) := by
  intro i j hij
  exact min_le_min_right N (Nat.mul_le_mul_right _ hij)

theorem regularDecomposition_sampledDepth_step_le (ε : ℝ) (N i : ℕ) :
    regularDecompositionSampledDepth ε N (i + 1) ≤
      regularDecompositionSampledDepth ε N i + regularDecompositionBlockLength ε N := by
  simp only [regularDecompositionSampledDepth, Nat.add_mul, Nat.one_mul]
  omega

theorem regularDecomposition_terminal_le_blocks_mul {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) :
    N ≤ regularDecompositionBlockCount ε N * regularDecompositionBlockLength ε N := by
  have hd : (0 : ℝ) < regularDecompositionBlockLength ε N :=
    Nat.cast_pos.mpr (regularDecomposition_blockLength_pos hεN)
  have hceil := Nat.le_ceil ((N : ℝ) / regularDecompositionBlockLength ε N)
  have hreal : (N : ℝ) ≤
      regularDecompositionBlockCount ε N * regularDecompositionBlockLength ε N :=
    (div_le_iff₀ hd).mp hceil
  exact_mod_cast hreal

theorem regularDecomposition_blockCount_pos {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) : 0 < regularDecompositionBlockCount ε N := by
  have hN : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    norm_num [this] at hεN
  have hblocks := regularDecomposition_terminal_le_blocks_mul hεN
  by_contra h
  have : regularDecompositionBlockCount ε N = 0 := by omega
  simp [this] at hblocks
  omega

theorem regularDecomposition_sampledDepth_terminal {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) :
    regularDecompositionSampledDepth ε N (regularDecompositionBlockCount ε N) = N := by
  exact min_eq_right (regularDecomposition_terminal_le_blocks_mul hεN)

/-- Every generation up to `N` lies between two consecutive sampled generations. -/
theorem regularDecomposition_sampledDepth_cover {ε : ℝ} {N n : ℕ}
    (hεN : 16 ≤ ε * N) (hn : n ≤ N) :
    ∃ i < regularDecompositionBlockCount ε N,
      regularDecompositionSampledDepth ε N i ≤ n ∧
        n ≤ regularDecompositionSampledDepth ε N (i + 1) := by
  let d := regularDecompositionBlockLength ε N
  let k := regularDecompositionBlockCount ε N
  have hd : 0 < d := regularDecomposition_blockLength_pos hεN
  have hk : 0 < k := regularDecomposition_blockCount_pos hεN
  have hblocks : N ≤ k * d := regularDecomposition_terminal_le_blocks_mul hεN
  by_cases hn' : n < N
  · refine ⟨n / d, (Nat.div_lt_iff_lt_mul hd).mpr (hn'.trans_le hblocks), ?_, ?_⟩
    · exact (min_le_left _ _).trans (Nat.div_mul_le_self n d)
    · apply Nat.le_min.mpr
      exact ⟨by simpa only [Nat.mul_comm d] using (Nat.lt_mul_div_succ n hd).le, hn⟩
  · have hnN : n = N := by omega
    subst n
    refine ⟨k - 1, by omega, regularDecomposition_sampledDepth_le ε N _, ?_⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact (regularDecomposition_sampledDepth_terminal hεN).ge

theorem regularDecomposition_sampledHeight_zero {ε : ℝ} {N : ℕ}
    (hεN : 16 ≤ ε * N) : regularDecompositionSampledHeight ε N 0 = 0 := by
  simp only [regularDecompositionSampledHeight, Nat.sub_zero,
    regularDecomposition_sampledDepth_terminal hεN, Nat.sub_self]

theorem regularDecomposition_sampledHeight_terminal (ε : ℝ) (N : ℕ) :
    regularDecompositionSampledHeight ε N (regularDecompositionBlockCount ε N) = N := by
  simp [regularDecompositionSampledHeight, regularDecomposition_sampledDepth_zero]

theorem regularDecomposition_sampledHeight_le (ε : ℝ) (N j : ℕ) :
    regularDecompositionSampledHeight ε N j ≤ N := Nat.sub_le _ _

theorem regularDecomposition_sampledHeight_monotone (ε : ℝ) (N : ℕ) :
    Monotone (regularDecompositionSampledHeight ε N) := by
  intro i j hij
  exact Nat.sub_le_sub_left (regularDecomposition_sampledDepth_monotone ε N
    (Nat.sub_le_sub_left hij _)) N

theorem regularDecomposition_sampledHeight_step_le (ε : ℝ) (N : ℕ) {j : ℕ}
    (hj : j < regularDecompositionBlockCount ε N) :
    regularDecompositionSampledHeight ε N (j + 1) ≤
      regularDecompositionSampledHeight ε N j + regularDecompositionBlockLength ε N := by
  have hi : regularDecompositionBlockCount ε N - (j + 1) + 1 =
      regularDecompositionBlockCount ε N - j := by omega
  have hstep := regularDecomposition_sampledDepth_step_le ε N
    (regularDecompositionBlockCount ε N - (j + 1))
  rw [hi] at hstep
  have hlo := regularDecomposition_sampledDepth_le ε N
    (regularDecompositionBlockCount ε N - (j + 1))
  have hhi := regularDecomposition_sampledDepth_le ε N
    (regularDecompositionBlockCount ε N - j)
  simp only [regularDecompositionSampledHeight]
  omega

theorem regularDecomposition_sampledHeight_gap_le (ε : ℝ) (N : ℕ) {j : ℕ}
    (hj : j < regularDecompositionBlockCount ε N) :
    regularDecompositionSampledHeight ε N (j + 1) -
      regularDecompositionSampledHeight ε N j ≤ regularDecompositionBlockLength ε N := by
  have h := regularDecomposition_sampledHeight_step_le ε N hj
  omega

/-- Every height above the terminal generation is bracketed by consecutive sampled heights. -/
theorem regularDecomposition_sampledHeight_cover {ε : ℝ} {N n : ℕ}
    (hεN : 16 ≤ ε * N) (hn : n ≤ N) :
    ∃ j < regularDecompositionBlockCount ε N,
      regularDecompositionSampledHeight ε N j ≤ n ∧
        n ≤ regularDecompositionSampledHeight ε N (j + 1) := by
  obtain ⟨i, hi, hlo, hhi⟩ :=
    regularDecomposition_sampledDepth_cover hεN (Nat.sub_le N n)
  let k := regularDecompositionBlockCount ε N
  have hindex₁ : k - (k - (i + 1)) = i + 1 := by omega
  have hindex₂ : k - (k - (i + 1) + 1) = i := by omega
  refine ⟨k - (i + 1), by omega, ?_, ?_⟩
  · change N - regularDecompositionSampledDepth ε N (k - (k - (i + 1))) ≤ n
    rw [hindex₁]
    omega
  · change n ≤ N - regularDecompositionSampledDepth ε N (k - (k - (i + 1) + 1))
    rw [hindex₂]
    have hbound := regularDecomposition_sampledDepth_le ε N i
    omega

theorem regularDecomposition_sampledHeight_add_depth (ε : ℝ) (N j : ℕ) :
    regularDecompositionSampledHeight ε N j +
      regularDecompositionSampledDepth ε N (regularDecompositionBlockCount ε N - j) = N := by
  exact Nat.sub_add_cancel (regularDecomposition_sampledDepth_le ε N _)

end FalconerThetaGauge
