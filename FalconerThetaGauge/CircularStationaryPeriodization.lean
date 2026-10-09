/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.CircularStationaryCutoff
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # The actual periodic stationary cutoff -/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace FalconerThetaGauge

/-- Periodize the literal compact cutoff by its integer translates through `2π`. -/
def circularStationaryPeriodicCutoff (K : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℤ, circularStationaryCutoff K (x - (n : ℝ) * (2 * Real.pi))

private theorem cutoff_other_translate_eq_zero (K : ℕ) (m n : ℤ) (hmn : n ≠ m)
    {x : ℝ} (hx : |x - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3) :
    circularStationaryCutoff K (x - (n : ℝ) * (2 * Real.pi)) = 0 := by
  apply circularStationaryCutoff_eq_zero
  have hxb := abs_lt.mp hx
  have hp := Real.pi_pos
  rcases lt_or_gt_of_ne hmn with hnm | hmn
  · have hi : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (show n + 1 ≤ m by omega)
    have hpos : Real.pi / 3 < x - (n : ℝ) * (2 * Real.pi) := by nlinarith
    exact hpos.trans_le (le_abs_self _)
  · have hi : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show m + 1 ≤ n by omega)
    have hneg : Real.pi / 3 < -(x - (n : ℝ) * (2 * Real.pi)) := by nlinarith
    exact hneg.trans_le (neg_le_abs _)

/-- On a chart wider than a period, all other translates vanish identically. -/
theorem circularStationaryPeriodicCutoff_eq_translate (K : ℕ) (m : ℤ) {x : ℝ}
    (hx : |x - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3) :
    circularStationaryPeriodicCutoff K x =
      circularStationaryCutoff K (x - (m : ℝ) * (2 * Real.pi)) := by
  exact tsum_eq_single m (fun n hn ↦ cutoff_other_translate_eq_zero K m n hn hx)

theorem exists_stationary_angle_chart (x : ℝ) :
    ∃ m : ℤ, |x - (m : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  have h := sub_toIocDiv_zsmul_mem_Ioc Real.two_pi_pos (-Real.pi) x
  rw [zsmul_eq_mul] at h
  exact abs_le.mpr ⟨h.1.le, by linarith [h.2]⟩

theorem circularStationaryPeriodicCutoff_eventuallyEq_translate (K : ℕ) (m : ℤ) {x : ℝ}
    (hx : |x - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3) :
    circularStationaryPeriodicCutoff K =ᶠ[𝓝 x]
      (fun y ↦ circularStationaryCutoff K (y - (m : ℝ) * (2 * Real.pi))) := by
  have hU : IsOpen {y : ℝ | |y - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3} :=
    isOpen_lt (continuous_id.sub continuous_const).abs continuous_const
  filter_upwards [hU.mem_nhds hx] with y hy
  exact circularStationaryPeriodicCutoff_eq_translate K m hy

theorem contDiff_circularStationaryPeriodicCutoff (K : ℕ) :
    ContDiff ℝ ∞ (circularStationaryPeriodicCutoff K) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨m, hm⟩ := exists_stationary_angle_chart x
  have hchart : |x - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3 := by
    linarith [Real.pi_pos]
  exact ((contDiff_circularStationaryCutoff K).comp
    (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq
      (circularStationaryPeriodicCutoff_eventuallyEq_translate K m hchart)

theorem circularStationaryPeriodicCutoff_periodic (K : ℕ) :
    Periodic (circularStationaryPeriodicCutoff K) (2 * Real.pi) := by
  intro x
  obtain ⟨m, hm⟩ := exists_stationary_angle_chart x
  have hx : |x - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3 := by
    linarith [Real.pi_pos]
  have heq : x + 2 * Real.pi - ((m + 1 : ℤ) : ℝ) * (2 * Real.pi) =
      x - (m : ℝ) * (2 * Real.pi) := by push_cast; ring
  rw [circularStationaryPeriodicCutoff_eq_translate K (m + 1) (by rwa [heq]),
    circularStationaryPeriodicCutoff_eq_translate K m hx, heq]

theorem circularStationaryPeriodicCutoff_mem_Icc (K : ℕ) (x : ℝ) :
    circularStationaryPeriodicCutoff K x ∈ Icc 0 1 := by
  obtain ⟨m, hm⟩ := exists_stationary_angle_chart x
  rw [circularStationaryPeriodicCutoff_eq_translate K m (by linarith [Real.pi_pos])]
  exact circularStationaryCutoff_mem_Icc K _

theorem norm_iteratedDeriv_circularStationaryPeriodicCutoff_le (K k : ℕ) (hk : k ≤ K)
    (x : ℝ) :
    ‖iteratedDeriv k (circularStationaryPeriodicCutoff K) x‖ ≤
      (2 * Real.pi) ^ k * (k.factorial : ℝ) ^ 2 := by
  obtain ⟨m, hm⟩ := exists_stationary_angle_chart x
  have hx : |x - (m : ℝ) * (2 * Real.pi)| < 5 * Real.pi / 3 := by
    linarith [Real.pi_pos]
  rw [(circularStationaryPeriodicCutoff_eventuallyEq_translate K m hx).iteratedDeriv_eq k,
    iteratedDeriv_comp_sub_const]
  exact norm_iteratedDeriv_circularStationaryCutoff_le K k hk _

end FalconerThetaGauge
