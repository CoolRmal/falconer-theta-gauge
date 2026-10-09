/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.CircularStationaryPartitionDerivatives
public import FalconerThetaGauge.NonstationaryPhasePeriodicUniform

/-! # The actual nonstationary remainder in the circular expansion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The literal circular phase, with its two stationary points at `φ₀` and `φ₀ + π`. -/
def circularOscillatoryPhase (Λ φ₀ φ : ℝ) : ℝ :=
  -Λ * Real.cos (φ - φ₀)

theorem contDiff_circularOscillatoryPhase (Λ φ₀ : ℝ) :
    ContDiff ℝ ∞ (circularOscillatoryPhase Λ φ₀) :=
  contDiff_const.mul (Real.contDiff_cos.comp (contDiff_id.sub contDiff_const))

theorem circularOscillatoryPhase_periodic (Λ φ₀ : ℝ) :
    Periodic (circularOscillatoryPhase Λ φ₀) (2 * Real.pi) := by
  intro φ
  simp only [circularOscillatoryPhase, add_sub_right_comm, Real.cos_add_two_pi]

theorem deriv_circularOscillatoryPhase (Λ φ₀ φ : ℝ) :
    deriv (circularOscillatoryPhase Λ φ₀) φ = Λ * Real.sin (φ - φ₀) := by
  have h := ((Real.hasDerivAt_cos (φ - φ₀)).comp φ
    ((hasDerivAt_id φ).sub_const φ₀)).const_mul (-Λ)
  change deriv (fun t ↦ -Λ * Real.cos (t - φ₀)) φ = _
  simpa only [Function.comp_apply, id_eq, mul_one, neg_mul, mul_neg, neg_neg] using h.deriv

theorem norm_iteratedDeriv_circularOscillatoryPhase_le {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (φ₀ : ℝ) (j : ℕ) (φ : ℝ) :
    ‖iteratedDeriv j (circularOscillatoryPhase Λ φ₀) φ‖ ≤ Λ := by
  change ‖iteratedDeriv j (fun t ↦ -Λ * Real.cos (t - φ₀)) φ‖ ≤ _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const,
    norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hΛ, Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_iteratedDeriv_cos_le_one j (φ - φ₀)) hΛ

/-- The true support of the away amplitude has an open neighborhood on which the
phase derivative is at least `Λ/3`. -/
theorem circularStationaryAwayCutoff_nonstationary_support (K : ℕ) (φ₀ : ℝ)
    (G : ℝ → ℂ) :
    tsupport (fun φ ↦ (circularStationaryAwayCutoff K φ₀ φ : ℂ) * G φ) ⊆
      {φ : ℝ | 1 / 3 < |Real.sin (φ - φ₀)|} := by
  have hcast : tsupport (fun φ ↦ (circularStationaryAwayCutoff K φ₀ φ : ℂ)) ⊆
      tsupport (circularStationaryAwayCutoff K φ₀) :=
    tsupport_comp_subset (g := fun t : ℝ ↦ (t : ℂ)) rfl _
  intro φ hφ
  have hcut := hcast (tsupport_mul_subset_left hφ)
  have hs := tsupport_circularStationaryAwayCutoff_subset K φ₀ hcut
  change 1 / 2 ≤ |Real.sin (φ - φ₀)| at hs
  change 1 / 3 < |Real.sin (φ - φ₀)|
  linarith [hs]

/-- The literal away integral obeys the periodic integration-by-parts estimate.
The cutoff contributes its proved scale `1 + 4πK²` to the amplitude scale. -/
theorem norm_circularStationaryAway_integral_le {Λ A M : ℝ} {K k : ℕ}
    (hΛ : 0 < Λ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hGP : Periodic G (2 * Real.pi)) (hreg : IsDerivativeRegular A M K G)
    (hk : k ≤ K) (φ₀ u : ℝ) :
    ‖∫ φ in u..u + 2 * Real.pi,
      Complex.exp ((circularOscillatoryPhase Λ φ₀ φ : ℝ) * Complex.I) *
        ((circularStationaryAwayCutoff K φ₀ φ : ℂ) * G φ)‖ ≤
      2 * Real.pi * A *
        (6 * (k + 1) ^ 2 * max (circularStationaryAwayDerivativeScale K + M) 3 / Λ) ^ k := by
  have hc := circularStationaryAwayCutoff_isDerivativeRegular K φ₀
  have hproduct := hc.mul hreg
  have hpreg : IsDerivativeRegular A (circularStationaryAwayDerivativeScale K + M) K
      (fun φ ↦ (circularStationaryAwayCutoff K φ₀ φ : ℂ) * G φ) := by
    have heq : ((fun φ ↦ (circularStationaryAwayCutoff K φ₀ φ : ℂ)) * G) =
        (fun φ ↦ (circularStationaryAwayCutoff K φ₀ φ : ℂ) * G φ) := by
      funext φ
      exact Pi.mul_apply _ _ _
    simpa only [one_mul, heq] using hproduct
  have hperiod : Periodic (fun φ ↦ (circularStationaryAwayCutoff K φ₀ φ : ℂ) * G φ)
      (2 * Real.pi) := by
    intro φ
    change (circularStationaryAwayCutoff K φ₀ (φ + 2 * Real.pi) : ℂ) *
      G (φ + 2 * Real.pi) = _
    rw [circularStationaryAwayCutoff_periodic K φ₀, hGP]
  have hU : IsOpen {φ : ℝ | 1 / 3 < |Real.sin (φ - φ₀)|} :=
    isOpen_lt continuous_const
      ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)
  have hlow : ∀ φ ∈ {φ : ℝ | 1 / 3 < |Real.sin (φ - φ₀)|},
      Λ / 3 ≤ ‖deriv (circularOscillatoryPhase Λ φ₀) φ‖ := by
    intro φ hφ
    rw [deriv_circularOscillatoryPhase, norm_mul, Real.norm_eq_abs, abs_of_pos hΛ,
      Real.norm_eq_abs]
    change 1 / 3 < |Real.sin (φ - φ₀)| at hφ
    nlinarith
  have h := nonstationary_phase_periodic (contDiff_circularOscillatoryPhase Λ φ₀)
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_circularStationaryAwayCutoff K φ₀)).mul hG)
    (circularOscillatoryPhase_periodic Λ φ₀) hperiod u hpreg hk
    (by positivity : 0 < Λ / 3) hΛ.le hU
    (circularStationaryAwayCutoff_nonstationary_support K φ₀ G) hlow
    (fun j _ _ φ _ ↦ norm_iteratedDeriv_circularOscillatoryPhase_le hΛ.le φ₀ j φ)
  have hratio : Λ / (Λ / 3) = (3 : ℝ) := by field_simp
  have hbase : 2 * (k + 1 : ℝ) ^ 2 *
      max (circularStationaryAwayDerivativeScale K + M) (Λ / (Λ / 3)) / (Λ / 3) =
      6 * (k + 1 : ℝ) ^ 2 *
        max (circularStationaryAwayDerivativeScale K + M) 3 / Λ := by
    rw [hratio]
    field_simp
    ring
  rw [hbase, abs_of_pos Real.two_pi_pos] at h
  exact h

end FalconerThetaGauge
