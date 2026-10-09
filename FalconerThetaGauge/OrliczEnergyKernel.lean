module

public import FalconerThetaGauge.OrliczEnergy
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Quantitative bounds for the dyadic Gaussian kernel

The finite-prefix and rescaled-tail estimates implement the scalar splitting
in the proof of Lemma 5.2. Their cutoff is a genuine natural-number index.
-/

@[expose] public section

open scoped BigOperators

namespace FalconerThetaGauge

theorem dyadicGaussianTerm_add_le (γ r : ℝ) (hγ : 0 ≤ γ) (n m : ℕ) :
    dyadicGaussianTerm γ r (n + m) ≤
      (((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m) *
        dyadicGaussianTerm γ ((2 : ℝ) ^ m * r) n := by
  have hw : ((n : ℝ) + m + 1) ^ γ ≤ (((m : ℝ) + 1) * ((n : ℝ) + 1)) ^ γ :=
    Real.rpow_le_rpow (by positivity)
      (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n)]) hγ
  rw [Real.mul_rpow (by positivity) (by positivity)] at hw
  have hsq : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
    rw [pow_two, ← mul_pow]
    norm_num
  have he : Real.exp (-((4 : ℝ) ^ (n + m) * r ^ 2)) =
      Real.exp (-((4 : ℝ) ^ n * ((2 : ℝ) ^ m * r) ^ 2)) := by
    congr 1
    rw [pow_add, mul_pow, hsq]
    ring
  unfold dyadicGaussianTerm
  rw [he]
  simp only [Nat.cast_add, pow_add]
  calc
    _ ≤ (((m : ℝ) + 1) ^ γ * ((n : ℝ) + 1) ^ γ) * ((2 : ℝ) ^ n * (2 : ℝ) ^ m) *
        Real.exp (-((4 : ℝ) ^ n * ((2 : ℝ) ^ m * r) ^ 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (by positivity)) (by positivity)
    _ = _ := by ring

theorem dyadicGaussianKernel_prefix_le (γ r : ℝ) (hγ : 0 ≤ γ) (m : ℕ) :
    ∑ n ∈ Finset.range m, dyadicGaussianTerm γ r n ≤ ((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m := by
  have hterm (n : ℕ) (hn : n ∈ Finset.range m) :
      dyadicGaussianTerm γ r n ≤ ((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ n := by
    have hnm : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast (Nat.add_le_add_right (Nat.le_of_lt (Finset.mem_range.mp hn)) 1)
    have hw := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ) + 1) hnm hγ
    have he : Real.exp (-((4 : ℝ) ^ n * r ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    calc
      dyadicGaussianTerm γ r n ≤ ((n : ℝ) + 1) ^ γ * (2 : ℝ) ^ n := by
        unfold dyadicGaussianTerm
        simpa using mul_le_mul_of_nonneg_left he
          (by positivity : 0 ≤ ((n : ℝ) + 1) ^ γ * (2 : ℝ) ^ n)
      _ ≤ _ := mul_le_mul_of_nonneg_right hw (by positivity)
  calc
    _ ≤ ∑ n ∈ Finset.range m, ((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ n := Finset.sum_le_sum hterm
    _ = ((m : ℝ) + 1) ^ γ * ∑ n ∈ Finset.range m, (2 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ ((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      norm_num

theorem dyadicGaussianKernel_tail_le (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 < r) (m : ℕ) :
    ∑' n, dyadicGaussianTerm γ r (n + m) ≤
      (((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m) * dyadicGaussianKernel γ ((2 : ℝ) ^ m * r) := by
  have hsum := summable_dyadicGaussianTerm γ r hγ hr
  have hscaled := summable_dyadicGaussianTerm γ ((2 : ℝ) ^ m * r) hγ (by positivity)
  have h := Summable.tsum_le_tsum (fun n ↦ dyadicGaussianTerm_add_le γ r hγ n m)
    ((summable_nat_add_iff m).mpr hsum) (hscaled.mul_left (((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m))
  simpa [dyadicGaussianKernel, tsum_mul_left] using h

theorem dyadicGaussianKernel_le_cutoff (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 < r) (m : ℕ)
    (hm : 1 ≤ (2 : ℝ) ^ m * r) :
    dyadicGaussianKernel γ r ≤
      (((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m) * (1 + dyadicGaussianKernel γ 1) := by
  have hsplit := (summable_dyadicGaussianTerm γ r hγ hr).sum_add_tsum_nat_add m
  calc
    dyadicGaussianKernel γ r = (∑ n ∈ Finset.range m, dyadicGaussianTerm γ r n) +
        ∑' n, dyadicGaussianTerm γ r (n + m) := hsplit.symm
    _ ≤ ((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m +
        (((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m) *
          dyadicGaussianKernel γ ((2 : ℝ) ^ m * r) :=
      add_le_add (dyadicGaussianKernel_prefix_le γ r hγ m) (dyadicGaussianKernel_tail_le γ r hγ hr m)
    _ ≤ ((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m +
        (((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m) * dyadicGaussianKernel γ 1 := by
      gcongr
      exact dyadicGaussianKernel_le_at_one γ _ hγ hm
    _ = _ := by ring

/-- A dyadic cutoff at the inverse radius, with an explicit logarithmic bound on its index. -/
theorem exists_dyadicGaussian_cutoff {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    ∃ m : ℕ, 1 ≤ (2 : ℝ) ^ m * r ∧ (2 : ℝ) ^ m ≤ 2 / r ∧
      (m : ℝ) + 1 ≤ (2 + (Real.log 2)⁻¹) * (1 + Real.log (1 / r)) := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 1 ≤ 1 / r := (one_le_div₀ hr).mpr hr₁.le
  have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg hx
  obtain ⟨m, hm₀, hm₁⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨m + 1, ((div_lt_iff₀ hr).mp hm₁).le, ?_, ?_⟩
  · rw [pow_succ]
    calc
      (2 : ℝ) ^ m * 2 ≤ (1 / r) * 2 := mul_le_mul_of_nonneg_right hm₀ (by norm_num)
      _ = 2 / r := by ring
  · have hindex := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ m) hm₀
    rw [Real.log_pow] at hindex
    have hm : (m : ℝ) ≤ Real.log (1 / r) / Real.log 2 := (le_div_iff₀ hlog₂).mpr hindex
    simp only [Nat.cast_add, Nat.cast_one]
    rw [div_eq_mul_inv] at hm
    nlinarith [inv_nonneg.mpr hlog₂.le,
      mul_nonneg (inv_nonneg.mpr hlog₂.le) hlog]

/-- An explicit finite constant for the scalar kernel bound in Lemma 5.2. -/
noncomputable def dyadicGaussianBoundConstant (γ : ℝ) : ℝ :=
  2 * (2 + (Real.log 2)⁻¹) ^ γ * (1 + dyadicGaussianKernel γ 1)

theorem dyadicGaussianBoundConstant_pos (γ : ℝ) : 0 < dyadicGaussianBoundConstant γ := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkernel := dyadicGaussianKernel_nonneg γ 1
  unfold dyadicGaussianBoundConstant
  positivity

/-- The actual small-radius scalar bound used by Lemma 5.2 of the manuscript. -/
theorem dyadicGaussianKernel_le_log (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 < r) (hr₁ : r < 1) :
    dyadicGaussianKernel γ r ≤
      dyadicGaussianBoundConstant γ * (1 + Real.log (1 / r)) ^ γ / r := by
  obtain ⟨m, hm₀, hm₁, hm₂⟩ := exists_dyadicGaussian_cutoff hr hr₁
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg ((one_le_div₀ hr).mpr hr₁.le)
  have hkernel := dyadicGaussianKernel_nonneg γ 1
  have hw := Real.rpow_le_rpow (by positivity : 0 ≤ (m : ℝ) + 1) hm₂ hγ
  rw [Real.mul_rpow (by positivity) (by positivity)] at hw
  calc
    dyadicGaussianKernel γ r ≤
        (((m : ℝ) + 1) ^ γ * (2 : ℝ) ^ m) * (1 + dyadicGaussianKernel γ 1) :=
      dyadicGaussianKernel_le_cutoff γ r hγ hr m hm₀
    _ ≤ ((2 + (Real.log 2)⁻¹) ^ γ * (1 + Real.log (1 / r)) ^ γ * (2 / r)) *
        (1 + dyadicGaussianKernel γ 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hw hm₁ (by positivity) (by positivity))
        (by positivity)
    _ = _ := by unfold dyadicGaussianBoundConstant; ring

end FalconerThetaGauge
