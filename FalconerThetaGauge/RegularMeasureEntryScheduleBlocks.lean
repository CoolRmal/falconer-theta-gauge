/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryBudget

/-!
# Actual marked blocks of depths

The interval `{0,…,N}` is partitioned into consecutive blocks of `q` depths.
One fixed minimizing depth is marked in every actual block.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- A fixed minimizing element of an actual nonempty finite set of depths. -/
def finiteProfileMinimizer (A : ℕ → ℝ) (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then (Finset.exists_mem_eq_inf' h A).choose else 0

theorem finiteProfileMinimizer_mem {A : ℕ → ℝ} {S : Finset ℕ} (hS : S.Nonempty) :
    finiteProfileMinimizer A S ∈ S := by
  rw [finiteProfileMinimizer, dite_eq_left hS]
  exact (Finset.exists_mem_eq_inf' hS A).choose_spec.1

theorem finiteProfileMinimizer_le {A : ℕ → ℝ} {S : Finset ℕ} (hS : S.Nonempty)
    {n : ℕ} (hn : n ∈ S) : A (finiteProfileMinimizer A S) ≤ A n := by
  rw [finiteProfileMinimizer, dite_eq_left hS,
    ← (Finset.exists_mem_eq_inf' hS A).choose_spec.2]
  exact Finset.inf'_le _ hn

/-- The first depth in block `b`. -/
def profileBlockStart (q b : ℕ) : ℕ := b * q

/-- The last depth in block `b`, truncating the last block at `N`. -/
def profileBlockEnd (q N b : ℕ) : ℕ := min ((b + 1) * q - 1) N

/-- An actual finite block of consecutive depths. -/
def profileDepthBlock (q N b : ℕ) : Finset ℕ :=
  Finset.Icc (profileBlockStart q b) (profileBlockEnd q N b)

/-- The minimizing depth marked in the actual block. -/
def profileMarkedDepth (A : ℕ → ℝ) (q N b : ℕ) : ℕ :=
  finiteProfileMinimizer A (profileDepthBlock q N b)

/-- The finite set of all marked depths through generation `N`. -/
def profileMarkedDepths (A : ℕ → ℝ) (q N : ℕ) : Finset ℕ :=
  (Finset.range (N / q + 1)).image (profileMarkedDepth A q N)

theorem profileBlockStart_mono (q : ℕ) : Monotone (profileBlockStart q) := by
  intro b c hbc
  exact Nat.mul_le_mul_right q hbc

theorem profileBlockEnd_mono (q N : ℕ) : Monotone (profileBlockEnd q N) := by
  intro b c hbc
  exact min_le_min_right N (Nat.sub_le_sub_right
    (Nat.mul_le_mul_right q (by omega : b + 1 ≤ c + 1)) 1)

theorem profileDepthBlock_nonempty {q N b : ℕ} (hq : 0 < q) (hb : b ≤ N / q) :
    (profileDepthBlock q N b).Nonempty := by
  have hstartN : b * q ≤ N :=
    (Nat.mul_le_mul_right q hb).trans (Nat.div_mul_le_self N q)
  apply Finset.nonempty_Icc.mpr
  unfold profileBlockStart profileBlockEnd
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Each depth belongs to its quotient-indexed actual block. -/
theorem mem_profileDepthBlock_quotient {q N n : ℕ} (hq : 0 < q) (hn : n ≤ N) :
    n ∈ profileDepthBlock q N (n / q) := by
  have hlo := Nat.div_mul_le_self n q
  have hhi := Nat.lt_mul_div_succ n hq
  rw [Nat.mul_comm q] at hhi
  apply Finset.mem_Icc.mpr
  unfold profileBlockStart profileBlockEnd
  omega

/-- Every depth in a block has that block's index as its quotient. -/
theorem div_eq_of_mem_profileDepthBlock {q N b n : ℕ} (hq : 0 < q)
    (hn : n ∈ profileDepthBlock q N b) : n / q = b := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hupper : n < (b + 1) * q := by
    dsimp [profileBlockEnd] at hhi
    have hraw := hhi.trans (min_le_left _ _)
    have hpos : 0 < (b + 1) * q := by positivity
    omega
  exact Nat.div_eq_of_lt_le (by simpa [profileBlockStart, Nat.mul_comm] using hlo)
    (by simpa only [Nat.mul_comm q] using hupper)

theorem profileMarkedDepth_spec {A : ℕ → ℝ} {q N b : ℕ}
    (hq : 0 < q) (hb : b ≤ N / q) :
    profileMarkedDepth A q N b ∈ profileDepthBlock q N b ∧
      ∀ n ∈ profileDepthBlock q N b, A (profileMarkedDepth A q N b) ≤ A n :=
  ⟨finiteProfileMinimizer_mem (profileDepthBlock_nonempty hq hb),
    fun _ hn ↦ finiteProfileMinimizer_le (profileDepthBlock_nonempty hq hb) hn⟩

theorem profileMarkedDepth_div {A : ℕ → ℝ} {q N b : ℕ}
    (hq : 0 < q) (hb : b ≤ N / q) : profileMarkedDepth A q N b / q = b :=
  div_eq_of_mem_profileDepthBlock hq (profileMarkedDepth_spec hq hb).1

theorem profileMarkedDepth_mem_markedDepths {A : ℕ → ℝ} {q N b : ℕ}
    (hb : b ≤ N / q) : profileMarkedDepth A q N b ∈ profileMarkedDepths A q N :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

theorem profileMarkedDepths_card_le (A : ℕ → ℝ) (q N : ℕ) :
    (profileMarkedDepths A q N).card ≤ N / q + 1 :=
  (Finset.card_image_le).trans (Finset.card_range _).le

/-- The actual finite marked-depth count satisfies the coefficient in Lemma 8.3. -/
theorem profileMarkedDepths_card_le_inverse_block (A : ℕ → ℝ) (θ : ℝ) {N : ℕ}
    (hN : 0 < N) : ((profileMarkedDepths A (blockCount θ N) N).card : ℝ) ≤
      1 / blockParameter θ N + 2 := by
  have hq : 0 < blockCount θ N := blockCount_pos θ hN
  have hq' : (0 : ℝ) < blockCount θ N := by exact_mod_cast hq
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv : (N / blockCount θ N : ℕ) * blockCount θ N ≤ N :=
    Nat.div_mul_le_self N _
  have hdiv' : ((N / blockCount θ N : ℕ) : ℝ) ≤ (N : ℝ) / blockCount θ N := by
    apply (le_div_iff₀ hq').mpr
    exact_mod_cast hdiv
  have hinverse : (N : ℝ) / blockCount θ N = 1 / blockParameter θ N := by
    unfold blockParameter
    field_simp
  have hcard : ((profileMarkedDepths A (blockCount θ N) N).card : ℝ) ≤
      ((N / blockCount θ N : ℕ) : ℝ) + 1 := by
    exact_mod_cast profileMarkedDepths_card_le A (blockCount θ N) N
  rw [hinverse] at hdiv'
  linarith

end FalconerThetaGauge
