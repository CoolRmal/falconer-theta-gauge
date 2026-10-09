module

public import FalconerThetaGauge.NonstationaryPhaseBounds

/-!
# Explicit derivatives of a reciprocal on the nonstationary region

Differentiating the actual reciprocal identity avoids introducing unspecified
smooth-extension constants. The factorial and geometric sum bound gives the
required polynomial derivative base.
-/

@[expose] public section

noncomputable section

open Set Finset Filter
open scoped Topology ContDiff

namespace FalconerThetaGauge

theorem choose_mul_factorial_le {n i : ℕ} (hi : i ≤ n) :
    n.choose i * i.factorial ≤ n.factorial := by
  have hpos := Nat.factorial_pos (n - i)
  have heq := Nat.choose_mul_factorial_mul_factorial hi
  nlinarith

theorem reciprocal_geometric_sum (L : ℝ) (j : ℕ) :
    L * (∑ i ∈ range j, (1 + L) ^ i) = (1 + L) ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- The actual reciprocal has a factorial derivative bound on every open
region where the original function has a lower bound and bounded derivatives. -/
theorem norm_iteratedDeriv_reciprocal_le {f q : ℝ → ℝ} {U : Set ℝ}
    (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q) (hU : IsOpen U)
    (hqf : ∀ x ∈ U, q x * f x = 1) {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    (hflow : ∀ x ∈ U, lam ≤ ‖f x‖) (N : ℕ)
    (hfder : ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U, ‖iteratedDeriv j f x‖ ≤ Λ) :
    ∀ j ≤ N, ∀ x ∈ U, ‖iteratedDeriv j q x‖ ≤ lam⁻¹ * (1 + Λ / lam) ^ j * j.factorial := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj x hx
    by_cases hjzero : j = 0
    · subst j
      simp only [iteratedDeriv_zero, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
      have hnorm : ‖q x‖ * ‖f x‖ = 1 := by
        rw [← norm_mul, hqf x hx, norm_one]
      have hb : ‖q x‖ ≤ 1 / lam := (le_div_iff₀ hlam).mpr
        ((mul_le_mul_of_nonneg_left (hflow x hx) (norm_nonneg (q x))).trans_eq hnorm)
      simpa only [one_div] using hb
    · have hjpos : 1 ≤ j := by omega
      let C := 1 + Λ / lam
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hlocal : (q * f) =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
        mem_of_superset (hU.mem_nhds hx) (fun y hy ↦ hqf y hy)
      have hder : iteratedDeriv j (q * f) x = 0 := by
        have heq := hlocal.iteratedDeriv_eq j
        simpa only [iteratedDeriv_const, ite_eq_right hjzero] using heq
      have hqj : ContDiffAt ℝ j q x := (hq.of_le (by exact_mod_cast le_top)).contDiffAt
      have hfj : ContDiffAt ℝ j f x := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      rw [iteratedDeriv_mul hqj hfj] at hder
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjzero
      rw [sum_range_succ] at hder
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        iteratedDeriv_zero] at hder
      have hlast : iteratedDeriv (m + 1) q x * f x =
          -(∑ i ∈ range (m + 1), ((m + 1).choose i : ℝ) *
            iteratedDeriv i q x * iteratedDeriv (m + 1 - i) f x) := by linarith
      have hnorm : ‖iteratedDeriv (m + 1) q x‖ * lam ≤
          Λ * lam⁻¹ * (m + 1).factorial * ∑ i ∈ range (m + 1), C ^ i := by
        calc
          _ ≤ ‖iteratedDeriv (m + 1) q x‖ * ‖f x‖ :=
            mul_le_mul_of_nonneg_left (hflow x hx) (norm_nonneg _)
          _ = ‖∑ i ∈ range (m + 1), ((m + 1).choose i : ℝ) *
              iteratedDeriv i q x * iteratedDeriv (m + 1 - i) f x‖ := by
            rw [← norm_mul, hlast, norm_neg]
          _ ≤ ∑ i ∈ range (m + 1), ‖((m + 1).choose i : ℝ) *
              iteratedDeriv i q x * iteratedDeriv (m + 1 - i) f x‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ range (m + 1), Λ * lam⁻¹ * (m + 1).factorial * C ^ i := by
            apply sum_le_sum
            intro i hi
            have him : i < m + 1 := mem_range.mp hi
            have hiq := ih i him (him.le.trans hj) x hx
            have hif := hfder (m + 1 - i) (by omega) ((Nat.sub_le _ _).trans hj) x hx
            have hchoose : ((m + 1).choose i : ℝ) * i.factorial ≤ (m + 1).factorial := by
              exact_mod_cast choose_mul_factorial_le him.le
            rw [norm_mul, norm_mul, Real.norm_natCast]
            calc
              _ ≤ ((m + 1).choose i : ℝ) * (lam⁻¹ * C ^ i * i.factorial) * Λ :=
                mul_le_mul
                  (mul_le_mul_of_nonneg_left hiq (Nat.cast_nonneg _)) hif
                  (norm_nonneg _) (by positivity)
              _ = (Λ * lam⁻¹ * C ^ i) * (((m + 1).choose i : ℝ) * i.factorial) := by ring
              _ ≤ (Λ * lam⁻¹ * C ^ i) * (m + 1).factorial :=
                mul_le_mul_of_nonneg_left hchoose (by positivity)
              _ = _ := by ring
          _ = _ := by rw [mul_sum]
      have hgeom : Λ * lam⁻¹ * (∑ i ∈ range (m + 1), C ^ i) = C ^ (m + 1) - 1 := by
        simpa only [C, div_eq_mul_inv] using reciprocal_geometric_sum (Λ / lam) (m + 1)
      have hfinal : ‖iteratedDeriv (m + 1) q x‖ * lam ≤
          C ^ (m + 1) * (m + 1).factorial := by
        calc
          _ ≤ (Λ * lam⁻¹ * ∑ i ∈ range (m + 1), C ^ i) * (m + 1).factorial := by
            convert hnorm using 1
            ring
          _ = (C ^ (m + 1) - 1) * (m + 1).factorial := by rw [hgeom]
          _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) (m + 1).factorial]
      have hdivide := (le_div_iff₀ hlam).mpr hfinal
      convert hdivide using 1
      dsimp [C]
      simp only [div_eq_mul_inv]
      ring

end FalconerThetaGauge
