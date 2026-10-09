module

public import FalconerThetaGauge.RadialProjectionPreparation
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Radial density domination under normalized restriction

Retaining at least one quarter of a probability's mass makes its normalized
restriction at most four times the original measure. This order survives the
actual radial pushforward, gives domination of its genuine Radon–Nikodym
density, and preserves the eighth-order Orlicz integral with an explicit cost.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- Monotonicity of actual Radon–Nikodym derivatives of finite measures. -/
theorem rnDeriv_le_of_measure_le {α : Type*} [MeasurableSpace α]
    (μ ν ξ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ξ]
    (hμν : μ ≤ ν) : μ.rnDeriv ξ ≤ᵐ[ξ] ν.rnDeriv ξ := by
  have h := Measure.rnDeriv_add (ν - μ) μ ξ
  rw [Measure.sub_add_cancel_of_le hμν] at h
  filter_upwards [h] with x hx
  rw [hx, Pi.add_apply]
  exact le_add_of_nonneg_left zero_le

/-- A finite scalar domination is inherited by the actual Radon–Nikodym densities. -/
theorem rnDeriv_le_mul_of_measure_le {α : Type*} [MeasurableSpace α]
    (μ ν ξ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ξ]
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hμν : μ ≤ c • ν) :
    μ.rnDeriv ξ ≤ᵐ[ξ] fun x ↦ c * ν.rnDeriv ξ x := by
  have : IsFiniteMeasure (c • ν) := Measure.smul_finite ν hc
  filter_upwards [rnDeriv_le_of_measure_le μ (c • ν) ξ hμν,
    Measure.rnDeriv_smul_left_of_ne_top ν ξ hc] with x hx heq
  simpa only [heq, Pi.smul_apply, smul_eq_mul] using hx

open GaugeSeparatedMeasures in
/-- Normalization of an actual quarter-mass restriction costs at most four. -/
theorem normalizedRestrict_le_four (μ : ProbabilityMeasure Plane) {A : Set Plane}
    (hmass : (1 / 4 : ℝ≥0∞) ≤ (μ : Measure Plane) A) :
    normalizedRestrict (μ : Measure Plane) A ≤ (4 : ℝ≥0∞) • (μ : Measure Plane) := by
  have hinv : ((μ : Measure Plane) A)⁻¹ ≤ 4 := by
    have h := ENNReal.inv_le_inv.mpr hmass
    norm_num at h ⊢
    exact h
  intro S
  rw [normalizedRestrict, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul' hinv (Measure.restrict_le_self S)

/-- Actual radial pushforward domination preserves both absolute continuity
and the kernel Radon–Nikodym bound, at each specified good pin. -/
theorem radialProjection_density_le_four
    (ν ν' : Measure Plane) [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hν : ν' ≤ (4 : ℝ≥0∞) • ν) (x : Plane)
    (hac : ν.map (radialProjection x) ≪ circleArcLength) :
    ν'.map (radialProjection x) ≪ circleArcLength ∧
      radialProjectionDensity ν' x ≤ᵐ[circleArcLength]
        fun w ↦ 4 * radialProjectionDensity ν x w := by
  have hmap : ν'.map (radialProjection x) ≤ (4 : ℝ≥0∞) • ν.map (radialProjection x) := by
    rw [← Measure.map_smul 4 measurable_radialProjection.of_uncurry_left.aemeasurable]
    exact Measure.map_mono hν measurable_radialProjection.of_uncurry_left
  have hac' : ν'.map (radialProjection x) ≪ circleArcLength :=
    (Measure.absolutelyContinuous_of_le hmap).trans (hac.smul_left 4)
  refine ⟨hac', ?_⟩
  have hle := rnDeriv_le_mul_of_measure_le (ν'.map (radialProjection x))
    (ν.map (radialProjection x)) circleArcLength (by simp) hmap
  have hnew := Kernel.rnDeriv_eq_rnDeriv_measure
    (κ := radialProjectionKernel ν') (η := Kernel.const Plane circleArcLength) (a := x)
  have hold := Kernel.rnDeriv_eq_rnDeriv_measure
    (κ := radialProjectionKernel ν) (η := Kernel.const Plane circleArcLength) (a := x)
  filter_upwards [hle, hnew, hold] with w hw hn ho
  exact hn.trans_le (hw.trans_eq (congrArg (fun t : ℝ≥0∞ ↦ 4 * t) ho.symm))

/-- The genuine radial Orlicz bound after a normalized quarter-mass restriction. -/
theorem lintegral_radialProjection_orlicz_le_four
    (ν ν' : Measure Plane) [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hν : ν' ≤ (4 : ℝ≥0∞) • ν) (x : Plane)
    (hac : ν.map (radialProjection x) ≪ circleArcLength) {γ : ℝ} (hγ : 0 ≤ γ) :
    (∫⁻ w, orliczPhiExtended γ (radialProjectionDensity ν' x w) ∂circleArcLength) ≤
      ENNReal.ofReal (4 * (1 + Real.log 4) ^ γ) *
        ∫⁻ w, orliczPhiExtended γ (radialProjectionDensity ν x w) ∂circleArcLength := by
  have hle := (radialProjection_density_le_four ν ν' hν x hac).2
  calc
    _ ≤ ∫⁻ w, orliczPhiExtended γ (4 * radialProjectionDensity ν x w) ∂circleArcLength :=
      lintegral_mono_ae (hle.mono fun w hw ↦ monotone_orliczPhiExtended hγ hw)
    _ ≤ ∫⁻ w, ENNReal.ofReal (4 * (1 + Real.log 4) ^ γ) *
        orliczPhiExtended γ (radialProjectionDensity ν x w) ∂circleArcLength := by
      apply lintegral_mono
      intro w
      simpa only [ENNReal.ofReal_ofNat] using
        orliczPhiExtended_mul_le hγ (D := 4) (by norm_num) (radialProjectionDensity ν x w)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end FalconerThetaGauge
