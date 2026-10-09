module

public import FalconerThetaGauge.StationaryMorseAmplitude
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Actual change of variables at a circular stationary point

The original localized cosine phase is an ordinary integral. Substitution
by the literal arcsine coordinate turns it into the actual compact quadratic
amplitude; the phase identity and the Jacobian are both proved.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

def localizedCircleIntegral (χ : ℝ → ℝ) (G : ℝ → ℂ) (φ₀ Λ : ℝ) : ℂ :=
  ∫ t : ℝ in -(Real.pi / 3)..Real.pi / 3,
    Complex.exp (-((Λ * Real.cos t : ℝ) : ℂ) * Complex.I) * (χ t : ℂ) * G (φ₀ + t)

theorem stationaryMorse_integrand_identity (χ : ℝ → ℝ) (G : ℝ → ℂ) (φ₀ Λ : ℝ)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    stationaryMorseJacobian s •
      (Complex.exp (-((Λ * Real.cos (stationaryMorseAngle s) : ℝ) : ℂ) * Complex.I) *
        (χ (stationaryMorseAngle s) : ℂ) * G (φ₀ + stationaryMorseAngle s)) =
      Complex.exp (-(Λ : ℂ) * Complex.I) *
        (Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) *
          stationaryMorseAmplitude χ G φ₀ s) := by
  have hcos := cos_stationaryMorseAngle
    (show s ∈ Icc (-2 : ℝ) 2 by constructor <;> linarith [hs.1, hs.2])
  have hphase :
      Complex.exp (-((Λ * Real.cos (stationaryMorseAngle s) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-(Λ : ℂ) * Complex.I) *
          Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, hcos]
    congr 1
    push_cast
    ring
  rw [hphase, Complex.real_smul]
  unfold stationaryMorseAmplitude
  ring

theorem localizedCircleIntegral_eq_quadratic {χ : ℝ → ℝ} {G : ℝ → ℂ}
    (hχsmooth : ContDiff ℝ ∞ χ) (hG : ContDiff ℝ ∞ G)
    (hχ : ∀ t : ℝ, Real.pi / 3 < |t| → χ t = 0) (φ₀ Λ : ℝ) :
    localizedCircleIntegral χ G φ₀ Λ = Complex.exp (-(Λ : ℂ) * Complex.I) *
      ∫ s : ℝ, Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) *
        stationaryMorseAmplitude χ G φ₀ s := by
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (f := stationaryMorseAngle) (f' := stationaryMorseJacobian)
    (g := fun t : ℝ ↦
      Complex.exp (-((Λ * Real.cos t : ℝ) : ℂ) * Complex.I) * (χ t : ℂ) * G (φ₀ + t))
    (a := -1) (b := 1)
    (fun s hs ↦ hasDerivAt_stationaryMorseAngle
      (by simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hs
          constructor <;> linarith [hs.1, hs.2]))
    (fun s hs ↦ (contDiffAt_stationaryMorseJacobian
      (by simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hs
          constructor <;> linarith [hs.1, hs.2])).continuousAt.continuousWithinAt)
    (by fun_prop)
  rw [stationaryMorseAngle_neg, stationaryMorseAngle_one] at hsub
  rw [localizedCircleIntegral, ← hsub]
  calc
    _ = ∫ s : ℝ in (-1)..1, Complex.exp (-(Λ : ℂ) * Complex.I) *
        (Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) *
          stationaryMorseAmplitude χ G φ₀ s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply stationaryMorse_integrand_identity
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
      have hsupport : support (fun s : ℝ ↦
          Complex.exp (((Λ / 2 * s ^ 2 : ℝ) : ℂ) * Complex.I) *
            stationaryMorseAmplitude χ G φ₀ s) ⊆ Icc (-1 : ℝ) 1 :=
        (support_mul_subset_right _ _).trans (support_stationaryMorseAmplitude_subset hχ G φ₀)
      rw [indicator_eq_self.mpr hsupport]

end FalconerThetaGauge
