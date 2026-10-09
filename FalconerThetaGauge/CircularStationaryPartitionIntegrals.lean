/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.CircularStationaryAway
public import FalconerThetaGauge.StationaryMorseSubstitution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # The exact stationary and away integral decomposition on the circle -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem circularStationaryNear_integral_eq_localized (K : ℕ) {G : ℝ → ℂ}
    (hGP : Periodic G (2 * Real.pi)) (φ₀ Λ u : ℝ) :
    (∫ φ in u..u + 2 * Real.pi,
      Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
        ((circularStationaryNearCutoff K φ₀ φ : ℂ) * G φ)) =
      localizedCircleIntegral (circularStationaryCutoff K) G φ₀ Λ := by
  let F : ℝ → ℂ := fun φ ↦
    Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
      ((circularStationaryNearCutoff K φ₀ φ : ℂ) * G φ)
  let f : ℝ → ℂ := fun t ↦
    Complex.exp (-((Λ * Real.cos t : ℝ) : ℂ) * Complex.I) *
      (circularStationaryCutoff K t : ℂ) * G (φ₀ + t)
  have hFP : Periodic F (2 * Real.pi) := by
    intro φ
    dsimp [F]
    rw [circularOscillatoryPhase_periodic Λ φ₀,
      circularStationaryNearCutoff_periodic K φ₀, hGP]
  have hfs : support f ⊆ Icc (-(Real.pi / 3)) (Real.pi / 3) := by
    intro t ht
    by_contra h
    have hz : circularStationaryCutoff K t = 0 := by
      by_contra hne
      exact h (support_circularStationaryCutoff_subset K hne)
    exact ht (by simp [f, hz])
  change (∫ φ in u..u + 2 * Real.pi, F φ) = _
  calc
    _ = ∫ φ in φ₀ - Real.pi..φ₀ + Real.pi, F φ := by
      have hend : φ₀ - Real.pi + 2 * Real.pi = φ₀ + Real.pi := by ring
      simpa only [hend] using hFP.intervalIntegral_add_eq u (φ₀ - Real.pi)
    _ = ∫ t in -Real.pi..Real.pi, F (φ₀ + t) := by
      simpa only [← sub_eq_add_neg, add_comm Real.pi φ₀] using
        (intervalIntegral.integral_comp_add_left F φ₀
          (a := -Real.pi) (b := Real.pi)).symm
    _ = ∫ t in -Real.pi..Real.pi, f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hb : |t| ≤ Real.pi := by
        simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
          mem_Icc, ← abs_le] using ht
      have hc := circularStationaryPeriodicCutoff_eq_translate K (0 : ℤ) (x := t)
        (by
          simp only [Int.cast_zero, zero_mul, sub_zero]
          linarith [Real.pi_pos])
      simp only [Int.cast_zero, zero_mul, sub_zero] at hc
      dsimp [F, f, circularOscillatoryPhase, circularStationaryNearCutoff]
      rw [add_sub_cancel_left, hc]
      push_cast
      simp only [neg_mul, mul_assoc]
    _ = ∫ t : ℝ, f t := by
      apply intervalIntegral.integral_eq_integral_of_support_subset
      intro t ht
      have hb := hfs ht
      constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
    _ = localizedCircleIntegral (circularStationaryCutoff K) G φ₀ Λ := by
      rw [localizedCircleIntegral]
      change (∫ t : ℝ, f t) = ∫ t in -(Real.pi / 3)..Real.pi / 3, f t
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc,
        indicator_eq_self.mpr hfs]

theorem circularStationaryOpposite_integral_eq_localized (K : ℕ) {G : ℝ → ℂ}
    (hGP : Periodic G (2 * Real.pi)) (φ₀ Λ u : ℝ) :
    (∫ φ in u..u + 2 * Real.pi,
      Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
        ((circularStationaryOppositeCutoff K φ₀ φ : ℂ) * G φ)) =
      localizedCircleIntegral (circularStationaryCutoff K) G (φ₀ + Real.pi) (-Λ) := by
  have hphase : circularOscillatoryPhase (-Λ) (φ₀ + Real.pi) =
      circularOscillatoryPhase Λ φ₀ := by
    funext φ
    simp only [circularOscillatoryPhase, neg_neg, sub_add_eq_sub_sub, Real.cos_sub_pi]
    ring
  have hcut : circularStationaryNearCutoff K (φ₀ + Real.pi) =
      circularStationaryOppositeCutoff K φ₀ := by
    funext φ
    simp only [circularStationaryNearCutoff, circularStationaryOppositeCutoff,
      sub_add_eq_sub_sub]
  simpa only [hphase, hcut] using
    circularStationaryNear_integral_eq_localized K hGP (φ₀ + Real.pi) (-Λ) u

theorem circularStationary_integral_partition (K : ℕ) {G : ℝ → ℂ}
    (hG : Continuous G) (φ₀ Λ u : ℝ) :
    (∫ φ in u..u + 2 * Real.pi,
      Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) * G φ) =
      (∫ φ in u..u + 2 * Real.pi,
        Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
          ((circularStationaryNearCutoff K φ₀ φ : ℂ) * G φ)) +
      (∫ φ in u..u + 2 * Real.pi,
        Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
          ((circularStationaryOppositeCutoff K φ₀ φ : ℂ) * G φ)) +
      (∫ φ in u..u + 2 * Real.pi,
        Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
          ((circularStationaryAwayCutoff K φ₀ φ : ℂ) * G φ)) := by
  have he : Continuous (fun φ ↦
      Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (contDiff_circularOscillatoryPhase Λ φ₀).continuous).mul continuous_const)
  have hint (c : ℝ → ℝ) (hc : Continuous c) : IntervalIntegrable
      (fun φ ↦ Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
        ((c φ : ℂ) * G φ)) volume u (u + 2 * Real.pi) := by
    convert (he.mul ((Complex.continuous_ofReal.comp hc).mul hG)).intervalIntegrable
      (μ := volume) u (u + 2 * Real.pi) using 1
    funext φ
    simp only [Pi.mul_apply, Function.comp_apply]
  have hn := hint _ (contDiff_circularStationaryNearCutoff K φ₀).continuous
  have ho := hint _ (contDiff_circularStationaryOppositeCutoff K φ₀).continuous
  have ha := hint _ (contDiff_circularStationaryAwayCutoff K φ₀).continuous
  rw [← intervalIntegral.integral_add hn ho, ← intervalIntegral.integral_add (hn.add ho) ha]
  apply intervalIntegral.integral_congr
  intro φ _
  simp only [circularStationaryAwayCutoff, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The full circle integral is the sum of the two literal Morse-localized integrals
and the actual nonstationary remainder. -/
theorem circularStationary_integral_eq_localized_add_away (K : ℕ) {G : ℝ → ℂ}
    (hG : Continuous G) (hGP : Periodic G (2 * Real.pi)) (φ₀ Λ u : ℝ) :
    (∫ φ in u..u + 2 * Real.pi,
      Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) * G φ) =
      localizedCircleIntegral (circularStationaryCutoff K) G φ₀ Λ +
      localizedCircleIntegral (circularStationaryCutoff K) G (φ₀ + Real.pi) (-Λ) +
      (∫ φ in u..u + 2 * Real.pi,
        Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
          ((circularStationaryAwayCutoff K φ₀ φ : ℂ) * G φ)) := by
  rw [circularStationary_integral_partition K hG,
    circularStationaryNear_integral_eq_localized K hGP,
    circularStationaryOpposite_integral_eq_localized K hGP]

end FalconerThetaGauge
