module

public import FalconerThetaGauge.QuadraticPhaseCompact
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The literal Morse coordinate for circular stationary phase
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace FalconerThetaGauge

def stationaryMorseAngle (s : ℝ) : ℝ := 2 * Real.arcsin (s / 2)

def stationaryMorseJacobian (s : ℝ) : ℝ := (Real.sqrt (1 - s ^ 2 / 4))⁻¹

theorem stationaryMorseAngle_zero : stationaryMorseAngle 0 = 0 := by
  simp [stationaryMorseAngle]

theorem stationaryMorseAngle_one : stationaryMorseAngle 1 = Real.pi / 3 := by
  have ha : Real.arcsin (1 / 2) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])]
  rw [stationaryMorseAngle, ha]
  ring

theorem stationaryMorseAngle_neg (s : ℝ) :
    stationaryMorseAngle (-s) = -stationaryMorseAngle s := by
  simp only [stationaryMorseAngle, neg_div, Real.arcsin_neg]
  ring

theorem pi_div_three_lt_stationaryMorseAngle {s : ℝ} (hs : 1 < s) :
    Real.pi / 3 < stationaryMorseAngle s := by
  have h : Real.pi / 6 < Real.arcsin (s / 2) :=
    (Real.lt_arcsin_iff_sin_lt' ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).mpr
      (by rw [Real.sin_pi_div_six]; linarith)
  unfold stationaryMorseAngle
  linarith

theorem pi_div_three_lt_abs_stationaryMorseAngle {s : ℝ} (hs : 1 < |s|) :
    Real.pi / 3 < |stationaryMorseAngle s| := by
  rcases lt_abs.mp hs with h | h
  · exact (pi_div_three_lt_stationaryMorseAngle h).trans_le (le_abs_self _)
  · have ha := pi_div_three_lt_stationaryMorseAngle h
    rw [stationaryMorseAngle_neg] at ha
    exact ha.trans_le (neg_le_abs _)

theorem contDiffAt_stationaryMorseAngle {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    ContDiffAt ℝ ∞ stationaryMorseAngle s := by
  exact contDiffAt_const.mul ((Real.contDiffAt_arcsin (by linarith [hs.1])
    (by linarith [hs.2])).comp s (contDiffAt_id.div_const _))

theorem hasDerivAt_stationaryMorseAngle {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt stationaryMorseAngle (stationaryMorseJacobian s) s := by
  have h := ((Real.hasDerivAt_arcsin (by linarith [hs.1] : s / 2 ≠ -1)
    (by linarith [hs.2] : s / 2 ≠ 1)).comp s ((hasDerivAt_id s).div_const 2)).const_mul 2
  convert h using 1
  · rfl
  · simp only [stationaryMorseJacobian, div_pow, one_div]
    norm_num
    ring

theorem deriv_stationaryMorseAngle {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    deriv stationaryMorseAngle s = stationaryMorseJacobian s :=
  (hasDerivAt_stationaryMorseAngle hs).deriv

theorem stationaryMorseJacobian_pos {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    0 < stationaryMorseJacobian s := by
  unfold stationaryMorseJacobian
  apply inv_pos.mpr (Real.sqrt_pos.mpr _)
  nlinarith [mul_pos (by linarith [hs.1] : 0 < s + 2)
    (by linarith [hs.2] : 0 < 2 - s)]

theorem contDiffAt_stationaryMorseJacobian {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) :
    ContDiffAt ℝ ∞ stationaryMorseJacobian s := by
  have hj := stationaryMorseJacobian_pos hs
  unfold stationaryMorseJacobian at hj ⊢
  apply ContDiffAt.inv
  · apply ContDiffAt.sqrt (by fun_prop)
    have hsq : 0 < 1 - s ^ 2 / 4 := by
      nlinarith [mul_pos (by linarith [hs.1] : 0 < s + 2)
        (by linarith [hs.2] : 0 < 2 - s)]
    exact hsq.ne'
  · exact (inv_pos.mp hj).ne'

theorem cos_stationaryMorseAngle {s : ℝ} (hs : s ∈ Icc (-2 : ℝ) 2) :
    Real.cos (stationaryMorseAngle s) = 1 - s ^ 2 / 2 := by
  rw [stationaryMorseAngle, Real.cos_two_mul]
  have htrig := Real.sin_sq_add_cos_sq (Real.arcsin (s / 2))
  rw [Real.sin_arcsin (by linarith [hs.1]) (by linarith [hs.2])] at htrig
  nlinarith

end FalconerThetaGauge
