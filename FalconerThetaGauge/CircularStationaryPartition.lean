/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.CircularStationaryPeriodization

/-! # The actual circular partition at the two stationary points -/

@[expose] public section

noncomputable section

open Set Function
open scoped ContDiff Topology

namespace FalconerThetaGauge

/-- The cutoff centered at `φ₀`, with period `2π`. -/
def circularStationaryNearCutoff (K : ℕ) (φ₀ φ : ℝ) : ℝ :=
  circularStationaryPeriodicCutoff K (φ - φ₀)

/-- The cutoff at the opposite stationary point `φ₀ + π`. -/
def circularStationaryOppositeCutoff (K : ℕ) (φ₀ φ : ℝ) : ℝ :=
  circularStationaryPeriodicCutoff K (φ - φ₀ - Real.pi)

/-- The literal away amplitude in the circular partition. -/
def circularStationaryAwayCutoff (K : ℕ) (φ₀ φ : ℝ) : ℝ :=
  1 - circularStationaryNearCutoff K φ₀ φ - circularStationaryOppositeCutoff K φ₀ φ

theorem circularStationaryPeriodicCutoff_eq_one (K : ℕ) (m : ℤ) {x : ℝ}
    (hx : |x - (m : ℝ) * (2 * Real.pi)| ≤ Real.pi / 6) :
    circularStationaryPeriodicCutoff K x = 1 := by
  rw [circularStationaryPeriodicCutoff_eq_translate K m (by linarith [Real.pi_pos])]
  exact circularStationaryCutoff_eq_one K hx

theorem circularStationaryPeriodicCutoff_ne_zero (K : ℕ) {x : ℝ}
    (hx : circularStationaryPeriodicCutoff K x ≠ 0) :
    ∃ m : ℤ, |x - (m : ℝ) * (2 * Real.pi)| ≤ Real.pi / 3 := by
  obtain ⟨m, hm⟩ := exists_stationary_angle_chart x
  refine ⟨m, ?_⟩
  by_contra h
  have heq := circularStationaryPeriodicCutoff_eq_translate K m
    (by linarith [Real.pi_pos] : |x - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3)
  exact hx (heq.trans (circularStationaryCutoff_eq_zero K (lt_of_not_ge h)))

theorem circularStationaryNearCutoff_mul_opposite_eq_zero (K : ℕ) (φ₀ φ : ℝ) :
    circularStationaryNearCutoff K φ₀ φ * circularStationaryOppositeCutoff K φ₀ φ = 0 := by
  by_cases hn : circularStationaryNearCutoff K φ₀ φ = 0
  · rw [hn, zero_mul]
  by_cases ho : circularStationaryOppositeCutoff K φ₀ φ = 0
  · rw [ho, mul_zero]
  obtain ⟨m, hm⟩ := circularStationaryPeriodicCutoff_ne_zero K hn
  obtain ⟨n, hh⟩ := circularStationaryPeriodicCutoff_ne_zero K ho
  have hmb := abs_le.mp hm
  have hnb := abs_le.mp hh
  rcases le_or_gt m n with hmn | hnm
  · have hi : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    nlinarith [Real.pi_pos]
  · have hi : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (show n + 1 ≤ m by omega)
    nlinarith [Real.pi_pos]

theorem circularStationaryAwayCutoff_mem_Icc (K : ℕ) (φ₀ φ : ℝ) :
    circularStationaryAwayCutoff K φ₀ φ ∈ Icc 0 1 := by
  have hn := circularStationaryPeriodicCutoff_mem_Icc K (φ - φ₀)
  have ho := circularStationaryPeriodicCutoff_mem_Icc K (φ - φ₀ - Real.pi)
  have hmul := circularStationaryNearCutoff_mul_opposite_eq_zero K φ₀ φ
  dsimp [circularStationaryAwayCutoff, circularStationaryNearCutoff,
    circularStationaryOppositeCutoff] at hmul ⊢
  rcases mul_eq_zero.mp hmul with h | h <;> rw [h] <;>
    constructor <;> linarith [hn.1, hn.2, ho.1, ho.2]

theorem contDiff_circularStationaryNearCutoff (K : ℕ) (φ₀ : ℝ) :
    ContDiff ℝ ∞ (circularStationaryNearCutoff K φ₀) :=
  (contDiff_circularStationaryPeriodicCutoff K).comp (contDiff_id.sub contDiff_const)

theorem contDiff_circularStationaryOppositeCutoff (K : ℕ) (φ₀ : ℝ) :
    ContDiff ℝ ∞ (circularStationaryOppositeCutoff K φ₀) :=
  (contDiff_circularStationaryPeriodicCutoff K).comp
    ((contDiff_id.sub contDiff_const).sub contDiff_const)

theorem contDiff_circularStationaryAwayCutoff (K : ℕ) (φ₀ : ℝ) :
    ContDiff ℝ ∞ (circularStationaryAwayCutoff K φ₀) :=
  (contDiff_const.sub (contDiff_circularStationaryNearCutoff K φ₀)).sub
    (contDiff_circularStationaryOppositeCutoff K φ₀)

theorem circularStationaryNearCutoff_periodic (K : ℕ) (φ₀ : ℝ) :
    Periodic (circularStationaryNearCutoff K φ₀) (2 * Real.pi) := by
  intro φ
  simpa only [circularStationaryNearCutoff, add_sub_right_comm] using
    circularStationaryPeriodicCutoff_periodic K (φ - φ₀)

theorem circularStationaryOppositeCutoff_periodic (K : ℕ) (φ₀ : ℝ) :
    Periodic (circularStationaryOppositeCutoff K φ₀) (2 * Real.pi) := by
  intro φ
  simpa only [circularStationaryOppositeCutoff, add_sub_right_comm] using
    circularStationaryPeriodicCutoff_periodic K (φ - φ₀ - Real.pi)

theorem circularStationaryAwayCutoff_periodic (K : ℕ) (φ₀ : ℝ) :
    Periodic (circularStationaryAwayCutoff K φ₀) (2 * Real.pi) := by
  intro φ
  dsimp [circularStationaryAwayCutoff]
  rw [circularStationaryNearCutoff_periodic K φ₀,
    circularStationaryOppositeCutoff_periodic K φ₀]

private theorem small_sin_near_integer_pi {x : ℝ} (hx : |Real.sin x| < 1 / 2) :
    ∃ m : ℤ, |x - (m : ℝ) * Real.pi| < Real.pi / 6 := by
  let m := toIocDiv Real.pi_pos (-(Real.pi / 2)) x
  have h := sub_toIocDiv_zsmul_mem_Ioc Real.pi_pos (-(Real.pi / 2)) x
  rw [zsmul_eq_mul] at h
  have hb : |x - (m : ℝ) * Real.pi| ≤ Real.pi / 2 :=
    abs_le.mpr ⟨h.1.le, by linarith [h.2]⟩
  refine ⟨m, ?_⟩
  have hs : |Real.sin (x - (m : ℝ) * Real.pi)| < 1 / 2 := by
    simpa only [Real.sin_sub_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul] using hx
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])] at hs
  by_contra hn
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ Real.pi / 6 by linarith [Real.pi_pos]) hb (le_of_not_gt hn)
  rw [Real.sin_pi_div_six] at hmono
  exact hs.not_ge hmono

theorem circularStationaryAwayCutoff_eq_zero_of_small_sin (K : ℕ) (φ₀ : ℝ) {φ : ℝ}
    (hφ : |Real.sin (φ - φ₀)| < 1 / 2) : circularStationaryAwayCutoff K φ₀ φ = 0 := by
  obtain ⟨m, hm⟩ := small_sin_near_integer_pi hφ
  have htwo := Int.emod_two_eq_zero_or_one m
  have heven : m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1 := by omega
  rcases heven with he | ho
  · have heq : φ - φ₀ - ((m / 2 : ℤ) : ℝ) * (2 * Real.pi) =
        φ - φ₀ - (m : ℝ) * Real.pi := by
      have hcast : (m : ℝ) = 2 * ((m / 2 : ℤ) : ℝ) := by exact_mod_cast he
      rw [hcast]
      ring
    have hn : circularStationaryNearCutoff K φ₀ φ = 1 :=
      circularStationaryPeriodicCutoff_eq_one K (m / 2) (by rw [heq]; exact hm.le)
    have hz := circularStationaryNearCutoff_mul_opposite_eq_zero K φ₀ φ
    rw [hn, one_mul] at hz
    simp [circularStationaryAwayCutoff, hn, hz]
  · have heq : φ - φ₀ - Real.pi - ((m / 2 : ℤ) : ℝ) * (2 * Real.pi) =
        φ - φ₀ - (m : ℝ) * Real.pi := by
      have hcast : (m : ℝ) = 2 * ((m / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast ho
      rw [hcast]
      ring
    have hh : circularStationaryOppositeCutoff K φ₀ φ = 1 :=
      circularStationaryPeriodicCutoff_eq_one K (m / 2) (by rw [heq]; exact hm.le)
    have hz := circularStationaryNearCutoff_mul_opposite_eq_zero K φ₀ φ
    rw [hh, mul_one] at hz
    simp [circularStationaryAwayCutoff, hh, hz]

theorem tsupport_circularStationaryAwayCutoff_subset (K : ℕ) (φ₀ : ℝ) :
    tsupport (circularStationaryAwayCutoff K φ₀) ⊆
      {φ : ℝ | 1 / 2 ≤ |Real.sin (φ - φ₀)|} := by
  apply closure_minimal
  · intro φ hφ
    by_contra h
    exact mem_support.mp hφ
      (circularStationaryAwayCutoff_eq_zero_of_small_sin K φ₀ (lt_of_not_ge h))
  · exact isClosed_le continuous_const
      ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)

end FalconerThetaGauge
