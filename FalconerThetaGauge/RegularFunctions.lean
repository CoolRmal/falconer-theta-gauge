module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Explicit derivative bounds for smooth amplitudes

The global real-line version of Definition 3.1 applies to compactly supported
smooth amplitudes and to periodic lifts of circular amplitudes. The product
bound retains the sum of the two derivative scales exactly.
-/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

/-- Uniform bounds on each actual iterated derivative up to the chosen order. -/
structure IsDerivativeRegular (A M : ℝ) (k : ℕ) (f : ℝ → ℂ) : Prop where
  amplitude_nonneg : 0 ≤ A
  one_le_scale : 1 ≤ M
  smooth : ContDiff ℝ k f
  bound : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ A * M ^ j

theorem IsDerivativeRegular.of_le {A M : ℝ} {k l : ℕ} {f : ℝ → ℂ}
    (hf : IsDerivativeRegular A M k f) (hl : l ≤ k) : IsDerivativeRegular A M l f := by
  refine ⟨hf.amplitude_nonneg, hf.one_le_scale, hf.smooth.of_le (by exact_mod_cast hl), ?_⟩
  intro j hj x
  exact hf.bound j (hj.trans hl) x

/-- Leibniz's formula gives the literal `(A*B, M+P)` amplitude bound. -/
theorem IsDerivativeRegular.mul {A B M P : ℝ} {k : ℕ} {f g : ℝ → ℂ}
    (hf : IsDerivativeRegular A M k f) (hg : IsDerivativeRegular B P k g) :
    IsDerivativeRegular (A * B) (M + P) k (f * g) := by
  refine ⟨mul_nonneg hf.amplitude_nonneg hg.amplitude_nonneg,
    by linarith [hf.one_le_scale, hg.one_le_scale], hf.smooth.mul hg.smooth, ?_⟩
  intro j hj x
  have hfj : ContDiffAt ℝ j f x := (hf.smooth.of_le (by exact_mod_cast hj)).contDiffAt
  have hgj : ContDiffAt ℝ j g x := (hg.smooth.of_le (by exact_mod_cast hj)).contDiffAt
  rw [iteratedDeriv_mul hfj hgj]
  calc
    _ ≤ ∑ i ∈ range (j + 1),
        ‖(j.choose i : ℂ) * iteratedDeriv i f x * iteratedDeriv (j - i) g x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ range (j + 1), (j.choose i : ℝ) * (A * M ^ i) * (B * P ^ (j - i)) := by
      apply sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hf.bound i (hij.trans hj) x) (Nat.cast_nonneg _))
        (hg.bound (j - i) ((Nat.sub_le j i).trans hj) x)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg hf.amplitude_nonneg (pow_nonneg (by linarith [hf.one_le_scale]) _)))
    _ = (A * B) * (M + P) ^ j := by
      rw [add_pow, mul_sum]
      apply sum_congr rfl
      intro i _
      ring

/-- A finite nonempty product retains the exact sum of derivative scales. -/
theorem IsDerivativeRegular.prod {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (hS : S.Nonempty) (A M : ι → ℝ) (f : ι → ℝ → ℂ) (k : ℕ)
    (hf : ∀ i ∈ S, IsDerivativeRegular (A i) (M i) k (f i)) :
    IsDerivativeRegular (∏ i ∈ S, A i) (∑ i ∈ S, M i) k (∏ i ∈ S, f i) := by
  induction S using Finset.induction with
  | empty => simp at hS
  | @insert i S hi ih =>
    by_cases hSempty : S = ∅
    · simpa [hSempty] using hf i (mem_insert_self _ _)
    · have hg := ih (Finset.nonempty_iff_ne_empty.mpr hSempty)
        (fun j hj ↦ hf j (mem_insert_of_mem hj))
      simpa only [prod_insert hi, sum_insert hi] using
        (hf i (mem_insert_self _ _)).mul hg

end FalconerThetaGauge
