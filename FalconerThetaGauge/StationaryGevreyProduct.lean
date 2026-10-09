module

public import FalconerThetaGauge.StationaryGevreyComposition
public import FalconerThetaGauge.RegularFunctions

/-! # Finite Leibniz bounds for actual Gevrey amplitudes -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

theorem factorial_pair_le (n i : ℕ) (hi : i ≤ n) :
    (i.factorial : ℝ) * ((n - i).factorial : ℝ) ≤ (n.factorial : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos n)
    (Nat.factorial_mul_factorial_dvd_factorial hi)

/-- Multiplication preserves the factorial-square bound and adds derivative scales. -/
theorem norm_iteratedDeriv_mul_le_gevrey {f g : ℝ → ℂ} {n : ℕ} {x A B C D : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfderiv : ∀ k, k ≤ n →
      ‖iteratedDeriv k f x‖ ≤ A * B ^ k * (k.factorial : ℝ) ^ 2)
    (hgderiv : ∀ k, k ≤ n →
      ‖iteratedDeriv k g x‖ ≤ C * D ^ k * (k.factorial : ℝ) ^ 2) :
    ‖iteratedDeriv n (f * g) x‖ ≤ (A * C) * (B + D) ^ n * (n.factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_mul hf hg]
  calc
    _ ≤ ∑ i ∈ range (n + 1),
        ‖(n.choose i : ℂ) * iteratedDeriv i f x * iteratedDeriv (n - i) g x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n + 1),
        (n.choose i : ℝ) * (A * B ^ i) * (C * D ^ (n - i)) * (n.factorial : ℝ) ^ 2 := by
      apply sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (n.choose i : ℝ) * (A * B ^ i * (i.factorial : ℝ) ^ 2) *
            (C * D ^ (n - i) * ((n - i).factorial : ℝ) ^ 2) := by
          gcongr
          · exact hfderiv i hin
          · exact hgderiv (n - i) (Nat.sub_le n i)
        _ = (n.choose i : ℝ) * (A * B ^ i) * (C * D ^ (n - i)) *
            ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) ^ 2 := by ring
        _ ≤ _ := by
          gcongr
          exact factorial_pair_le n i hin
    _ = _ := by
      rw [add_pow, mul_sum, sum_mul]
      apply sum_congr rfl
      intro i _
      ring

end FalconerThetaGauge
