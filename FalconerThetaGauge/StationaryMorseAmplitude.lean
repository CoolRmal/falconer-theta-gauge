module

public import FalconerThetaGauge.StationaryMorseAngle

/-!
# The actual smooth compact amplitude after the circular Morse substitution

The arcsine singularities lie outside the localized support. The literal
product therefore extends smoothly by zero and is supported in [-1,1].
-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped ContDiff Topology

namespace FalconerThetaGauge

def stationaryMorseAmplitude (χ : ℝ → ℝ) (G : ℝ → ℂ) (φ₀ s : ℝ) : ℂ :=
  (χ (stationaryMorseAngle s) : ℂ) * G (φ₀ + stationaryMorseAngle s) *
    (stationaryMorseJacobian s : ℂ)

theorem stationaryMorseAmplitude_eq_zero {χ : ℝ → ℝ}
    (hχ : ∀ t : ℝ, Real.pi / 3 < |t| → χ t = 0) (G : ℝ → ℂ) (φ₀ : ℝ)
    {s : ℝ} (hs : 1 < |s|) : stationaryMorseAmplitude χ G φ₀ s = 0 := by
  simp only [stationaryMorseAmplitude,
    hχ _ (pi_div_three_lt_abs_stationaryMorseAngle hs), Complex.ofReal_zero, zero_mul]

theorem contDiff_stationaryMorseAmplitude {χ : ℝ → ℝ} {G : ℝ → ℂ}
    (hχsmooth : ContDiff ℝ ∞ χ) (hG : ContDiff ℝ ∞ G)
    (hχ : ∀ t : ℝ, Real.pi / 3 < |t| → χ t = 0) (φ₀ : ℝ) :
    ContDiff ℝ ∞ (stationaryMorseAmplitude χ G φ₀) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ Ioo (-2 : ℝ) 2
  · have hangle := contDiffAt_stationaryMorseAngle hs
    have hjac := contDiffAt_stationaryMorseJacobian hs
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp s
      (hχsmooth.contDiffAt.comp s hangle)).mul
        (hG.contDiffAt.comp s (contDiffAt_const.add hangle))).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp s hjac)
  · have hlarge : 1 < |s| := by
      simp only [mem_Ioo, not_and_or, not_lt] at hs
      rcases hs with hs | hs
      · linarith [neg_le_abs s]
      · linarith [le_abs_self s]
    have hnh : ∀ᶠ t in 𝓝 s, 1 < |t| :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hlarge
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hnh] with t ht
    exact stationaryMorseAmplitude_eq_zero hχ G φ₀ ht

theorem support_stationaryMorseAmplitude_subset {χ : ℝ → ℝ}
    (hχ : ∀ t : ℝ, Real.pi / 3 < |t| → χ t = 0) (G : ℝ → ℂ) (φ₀ : ℝ) :
    support (stationaryMorseAmplitude χ G φ₀) ⊆ Icc (-1 : ℝ) 1 := by
  apply support_subset_iff'.mpr
  intro s hs
  have hlarge : 1 < |s| := by
    apply lt_of_not_ge
    intro h
    exact hs (abs_le.mp h)
  exact stationaryMorseAmplitude_eq_zero hχ G φ₀ hlarge

theorem hasCompactSupport_stationaryMorseAmplitude {χ : ℝ → ℝ}
    (hχ : ∀ t : ℝ, Real.pi / 3 < |t| → χ t = 0) (G : ℝ → ℂ) (φ₀ : ℝ) :
    HasCompactSupport (stationaryMorseAmplitude χ G φ₀) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_stationaryMorseAmplitude_subset hχ G φ₀)

end FalconerThetaGauge
