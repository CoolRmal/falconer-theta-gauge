/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.CircularStationaryPartition
public import FalconerThetaGauge.RegularFunctions

/-! # The derivative scale of the actual away cutoff -/

@[expose] public section

noncomputable section

open Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem norm_iteratedDeriv_circularStationaryNearCutoff_le (K k : ℕ) (hk : k ≤ K)
    (φ₀ φ : ℝ) :
    ‖iteratedDeriv k (circularStationaryNearCutoff K φ₀) φ‖ ≤
      (2 * Real.pi) ^ k * (k.factorial : ℝ) ^ 2 := by
  change ‖iteratedDeriv k
    (fun t ↦ circularStationaryPeriodicCutoff K (t - φ₀)) φ‖ ≤ _
  rw [iteratedDeriv_comp_sub_const]
  exact norm_iteratedDeriv_circularStationaryPeriodicCutoff_le K k hk _

theorem norm_iteratedDeriv_circularStationaryOppositeCutoff_le (K k : ℕ) (hk : k ≤ K)
    (φ₀ φ : ℝ) :
    ‖iteratedDeriv k (circularStationaryOppositeCutoff K φ₀) φ‖ ≤
      (2 * Real.pi) ^ k * (k.factorial : ℝ) ^ 2 := by
  change ‖iteratedDeriv k
    (fun t ↦ circularStationaryPeriodicCutoff K (t - φ₀ - Real.pi)) φ‖ ≤ _
  have heq : (fun t ↦ circularStationaryPeriodicCutoff K (t - φ₀ - Real.pi)) =
      (fun t ↦ circularStationaryPeriodicCutoff K (t - (φ₀ + Real.pi))) := by
    funext t
    congr 1
    ring
  rw [heq, iteratedDeriv_comp_sub_const]
  exact norm_iteratedDeriv_circularStationaryPeriodicCutoff_le K k hk _

theorem norm_iteratedDeriv_circularStationaryAwayCutoff_le (K k : ℕ) (hk : k ≤ K)
    (φ₀ φ : ℝ) :
    ‖iteratedDeriv k (circularStationaryAwayCutoff K φ₀) φ‖ ≤
      if k = 0 then 1 else 2 * ((2 * Real.pi) ^ k * (k.factorial : ℝ) ^ 2) := by
  by_cases hzero : k = 0
  · subst k
    have hb := circularStationaryAwayCutoff_mem_Icc K φ₀ φ
    simpa only [iteratedDeriv_zero, Real.norm_eq_abs, abs_of_nonneg hb.1, ite_true] using hb.2
  have hn : ContDiffAt ℝ k (circularStationaryNearCutoff K φ₀) φ :=
    ((contDiff_circularStationaryNearCutoff K φ₀).of_le (by simp)).contDiffAt
  have ho : ContDiffAt ℝ k (circularStationaryOppositeCutoff K φ₀) φ :=
    ((contDiff_circularStationaryOppositeCutoff K φ₀).of_le (by simp)).contDiffAt
  change ‖iteratedDeriv k
    (fun t ↦ 1 - circularStationaryNearCutoff K φ₀ t -
      circularStationaryOppositeCutoff K φ₀ t) φ‖ ≤ _
  rw [iteratedDeriv_fun_sub (contDiffAt_const.sub hn) ho,
    iteratedDeriv_fun_sub contDiffAt_const hn, iteratedDeriv_const,
    ite_eq_right hzero, zero_sub, ite_eq_right hzero]
  calc
    _ ≤ ‖-iteratedDeriv k (circularStationaryNearCutoff K φ₀) φ‖ +
        ‖iteratedDeriv k (circularStationaryOppositeCutoff K φ₀) φ‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_neg]
      linarith [norm_iteratedDeriv_circularStationaryNearCutoff_le K k hk φ₀ φ,
        norm_iteratedDeriv_circularStationaryOppositeCutoff_le K k hk φ₀ φ]

/-- An explicit finite-order derivative scale for the literal circular remainder. -/
def circularStationaryAwayDerivativeScale (K : ℕ) : ℝ :=
  1 + 4 * Real.pi * (K : ℝ) ^ 2

theorem circularStationaryAwayCutoff_isDerivativeRegular (K : ℕ) (φ₀ : ℝ) :
    IsDerivativeRegular 1 (circularStationaryAwayDerivativeScale K) K
      (fun φ ↦ (circularStationaryAwayCutoff K φ₀ φ : ℂ)) := by
  have hf := contDiff_circularStationaryAwayCutoff K φ₀
  refine ⟨by norm_num,
    by dsimp [circularStationaryAwayDerivativeScale];
       exact le_add_of_nonneg_right (by positivity),
    (Complex.ofRealCLM.contDiff.comp hf).of_le (by simp), ?_⟩
  intro j hj φ
  have heq : iteratedDeriv j (fun t ↦ (circularStationaryAwayCutoff K φ₀ t : ℂ)) φ =
      ((iteratedDeriv j (circularStationaryAwayCutoff K φ₀) φ : ℝ) : ℂ) := by
    simpa only [Complex.real_smul, mul_one] using
      iteratedDeriv_smul_const ((hf.of_le (by simp)).contDiffAt) (1 : ℂ)
  rw [heq, Complex.norm_real, one_mul]
  by_cases hjzero : j = 0
  · simpa only [hjzero, ite_true, pow_zero] using
      norm_iteratedDeriv_circularStationaryAwayCutoff_le K j hj φ₀ φ
  have hfct : (j.factorial : ℝ) ≤ (K : ℝ) ^ j := by
    exact_mod_cast (Nat.factorial_le_pow j).trans (Nat.pow_le_pow_left hj j)
  have hB : 0 ≤ 2 * Real.pi * (K : ℝ) ^ 2 := by positivity
  have hpow : (2 : ℝ) ≤ 2 ^ j := le_self_pow₀ (by norm_num) (by omega)
  calc
    _ ≤ 2 * ((2 * Real.pi) ^ j * (j.factorial : ℝ) ^ 2) := by
      simpa only [ite_eq_right hjzero] using
        norm_iteratedDeriv_circularStationaryAwayCutoff_le K j hj φ₀ φ
    _ ≤ 2 * ((2 * Real.pi) ^ j * ((K : ℝ) ^ j) ^ 2) := by
      gcongr
    _ = 2 * (2 * Real.pi * (K : ℝ) ^ 2) ^ j := by
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm j 2]
    _ ≤ 2 ^ j * (2 * Real.pi * (K : ℝ) ^ 2) ^ j :=
      mul_le_mul_of_nonneg_right hpow (pow_nonneg hB j)
    _ = (4 * Real.pi * (K : ℝ) ^ 2) ^ j := by rw [← mul_pow]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
      (by dsimp [circularStationaryAwayDerivativeScale]; linarith) j

end FalconerThetaGauge
