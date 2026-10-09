/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureExcessMass
public import FalconerThetaGauge.Parameters

/-!
# The actual excess function of a unit-square probability

The definition uses the largest actual cell mass. Dyadic refinement gives the
exact Lipschitz constant `1/N`, independently of regular decomposition.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The manuscript's excess function determined by the heaviest actual dyadic cell. -/
def regularMeasureExcess (μ : Measure Plane) (N n : ℕ) : ℝ :=
  -(Real.log (maxCellMass μ n) / Real.log 2 + n) / N

theorem regularMeasureExcess_zero (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) (N : ℕ) : regularMeasureExcess μ N 0 = 0 := by
  simp [regularMeasureExcess, maxCellMass_zero μ hμ]

/-- The largest mass satisfies the defining identity `M(n)=2^(-n)R^(-A(n))`. -/
theorem maxCellMass_eq_power_excess (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    maxCellMass μ n = (2 : ℝ) ^ (-(n : ℝ)) *
      (2 : ℝ) ^ (-(N : ℝ) * regularMeasureExcess μ N n) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hexp : -(n : ℝ) + -(N : ℝ) * regularMeasureExcess μ N n =
      Real.log (maxCellMass μ n) / Real.log 2 := by
    unfold regularMeasureExcess
    field_simp
    ring
  rw [← Real.rpow_add (by norm_num), hexp, Real.rpow_def_of_pos (by norm_num),
    mul_comm (Real.log 2), div_mul_cancel₀ _ hlog, Real.exp_log (maxCellMass_pos μ hμ n)]

/-- The one-generation difference is at most `1/N`. -/
theorem regularMeasureExcess_step_le (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    |regularMeasureExcess μ N (n + 1) - regularMeasureExcess μ N n| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp := maxCellMass_pos μ hμ n
  have hp' := maxCellMass_pos μ hμ (n + 1)
  have hmono := Real.log_le_log hp' (maxCellMass_succ_le μ n)
  have hfour := Real.log_le_log hp (maxCellMass_le_four_mul_succ μ n)
  rw [Real.log_mul (by norm_num) hp'.ne'] at hfour
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlogfour] at hfour
  have hlo : 0 ≤ Real.log (maxCellMass μ n) / Real.log 2 -
      Real.log (maxCellMass μ (n + 1)) / Real.log 2 :=
    sub_nonneg.mpr (div_le_div_of_nonneg_right hmono hlog.le)
  have hhi : Real.log (maxCellMass μ n) / Real.log 2 -
      Real.log (maxCellMass μ (n + 1)) / Real.log 2 ≤ 2 := by
    rw [← sub_div]
    exact (div_le_iff₀ hlog).mpr (by linarith)
  have hstep : regularMeasureExcess μ N (n + 1) - regularMeasureExcess μ N n =
      (Real.log (maxCellMass μ n) / Real.log 2 -
        Real.log (maxCellMass μ (n + 1)) / Real.log 2 - 1) / N := by
    unfold regularMeasureExcess
    push_cast
    ring
  rw [hstep, abs_div, abs_of_pos hN']
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) hN'.le

/-- The actual excess function has the Lipschitz bound stated in Lemma 5.10(ii). -/
theorem regularMeasureExcess_lipschitz (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) {N : ℕ} (hN : 0 < N) (n m : ℕ) :
    |regularMeasureExcess μ N n - regularMeasureExcess μ N m| ≤
      |(n : ℝ) - m| / N := by
  have hordered : ∀ m n : ℕ, n ≤ m →
      |regularMeasureExcess μ N m - regularMeasureExcess μ N n| ≤ ((m : ℝ) - n) / N := by
    intro m
    induction m with
    | zero =>
      intro n hn
      have : n = 0 := by omega
      simp [this]
    | succ m ih =>
      intro n hn
      by_cases hnm : n ≤ m
      · calc
          _ ≤ |regularMeasureExcess μ N (m + 1) - regularMeasureExcess μ N m| +
              |regularMeasureExcess μ N m - regularMeasureExcess μ N n| := abs_sub_le _ _ _
          _ ≤ 1 / (N : ℝ) + ((m : ℝ) - n) / N :=
            add_le_add (regularMeasureExcess_step_le μ hμ hN m) (ih n hnm)
          _ = _ := by push_cast; ring
      · have : n = m + 1 := by omega
        simp [this]
  by_cases hnm : n ≤ m
  · have hreal : (n : ℝ) ≤ m := by exact_mod_cast hnm
    rw [abs_sub_comm (regularMeasureExcess μ N n), abs_sub_comm (n : ℝ),
      abs_of_nonneg (sub_nonneg.mpr hreal)]
    exact hordered m n hnm
  · have hmn : m ≤ n := by omega
    have hreal : (m : ℝ) ≤ n := by exact_mod_cast hmn
    rw [abs_of_nonneg (sub_nonneg.mpr hreal)]
    exact hordered n m hmn

/-- The zero-generation identity and Lipschitz bound give Lemma 5.10(iv). -/
theorem regularMeasureExcess_le_generation (μ : Measure Plane) [IsProbabilityMeasure μ]
    (hμ : μ unitSquare = 1) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    regularMeasureExcess μ N n ≤ (n : ℝ) / N := by
  have h := regularMeasureExcess_lipschitz μ hμ hN n 0
  simp only [regularMeasureExcess_zero μ hμ N, sub_zero, Nat.cast_zero,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at h
  exact (le_abs_self _).trans h

end FalconerThetaGauge
