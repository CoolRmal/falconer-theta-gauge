module

public import FalconerThetaGauge.RadialProjectionUniformIntegrability
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Absolute continuity of a weak radial measure limit

This file proves the measure-theoretic passage to a weak limit. A uniform
logarithmic Orlicz bound yields a quantitative bound on open sets by
Portmanteau. Outer regularity of the reference measure extends that bound
to arbitrary sets, and its vanishing tail proves absolute continuity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- An open-set cutoff bound extends to all sets for an outer regular reference measure. -/
theorem measure_le_cutoff_of_open {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    (σ ξ : Measure α) [ξ.OuterRegular] {H : ℝ} (hH : 0 < H) {T : ℝ≥0∞}
    (hopen : ∀ U : Set α, IsOpen U → σ U ≤ ENNReal.ofReal H * ξ U + T)
    (A : Set α) : σ A ≤ ENNReal.ofReal H * ξ A + T := by
  by_cases hA : ξ A = ∞
  · simp [hA, (ENNReal.ofReal_pos.mpr hH).ne', ENNReal.mul_top]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / H)
  have hδ : δ ≠ 0 := (ENNReal.ofReal_pos.mpr (div_pos hε hH)).ne'
  obtain ⟨U, hAU, hU, hξU⟩ := A.exists_isOpen_lt_add (μ := ξ) hA hδ
  have hcancel : ENNReal.ofReal H * δ = ε := by
    dsimp only [δ]
    rw [← ENNReal.ofReal_mul hH.le]
    have hreal : H * ((ε : ℝ) / H) = ε := by field_simp
    rw [hreal, ENNReal.ofReal_coe_nnreal]
  calc
    σ A ≤ σ U := measure_mono hAU
    _ ≤ ENNReal.ofReal H * ξ U + T := hopen U hU
    _ ≤ ENNReal.ofReal H * (ξ A + δ) + T := by gcongr
    _ = (ENNReal.ofReal H * ξ A + T) + ε := by rw [mul_add, hcancel]; ac_rfl

/-- Every weak probability limit inherits the explicit uniform cutoff estimate. -/
theorem measure_le_cutoff_of_tendsto_of_orlicz {α : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [HasOuterApproxClosed α] (ξ : Measure α) [ξ.OuterRegular]
    {σ : ProbabilityMeasure α} {σn : ℕ → ProbabilityMeasure α}
    {fn : ℕ → α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) {K : ℝ≥0∞}
    (hdensity : ∀ n, (σn n : Measure α) = ξ.withDensity (fn n))
    (hbound : ∀ n, (∫⁻ x, orliczPhiExtended p (fn n x) ∂ξ) ≤ K)
    (hconv : Tendsto σn atTop (𝓝 σ)) {H : ℝ} (hH : 0 < H) (A : Set α) :
    (σ : Measure α) A ≤ ENNReal.ofReal H * ξ A + orliczTailCoefficient p H * K := by
  apply measure_le_cutoff_of_open _ ξ hH
  intro U hU
  calc
    (σ : Measure α) U ≤ atTop.liminf (fun n ↦ (σn n : Measure α) U) :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hU
    _ ≤ ENNReal.ofReal H * ξ U + orliczTailCoefficient p H * K := by
      have hn : ∀ n, (σn n : Measure α) U ≤
          ENNReal.ofReal H * ξ U + orliczTailCoefficient p H * K := by
        intro n
        rw [hdensity n]
        exact withDensity_le_cutoff_add_orlicz ξ hp hH (hbound n) hU.measurableSet
      simpa only [liminf_const] using
        (liminf_le_liminf (f := atTop) (Eventually.of_forall hn))

/-- Uniform logarithmic moments of positive order force a weak limit to have an actual density. -/
theorem absolutelyContinuous_of_tendsto_of_uniform_orlicz {α : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [HasOuterApproxClosed α] (ξ : Measure α) [ξ.OuterRegular]
    {σ : ProbabilityMeasure α} {σn : ℕ → ProbabilityMeasure α}
    {fn : ℕ → α → ℝ≥0∞} {p : ℝ} (hp : 0 < p) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hdensity : ∀ n, (σn n : Measure α) = ξ.withDensity (fn n))
    (hbound : ∀ n, (∫⁻ x, orliczPhiExtended p (fn n x) ∂ξ) ≤ K)
    (hconv : Tendsto σn atTop (𝓝 σ)) : (σ : Measure α) ≪ ξ := by
  intro A hA
  have htail : Tendsto (fun H ↦ orliczTailCoefficient p H * K) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const (tendsto_orliczTailCoefficient hp) (Or.inr hK)
  have hmass : ∀ᶠ H : ℝ in atTop, (σ : Measure α) A ≤ orliczTailCoefficient p H * K := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    simpa only [hA, mul_zero, zero_add] using
      measure_le_cutoff_of_tendsto_of_orlicz ξ hp.le hdensity hbound hconv hH A
  exact le_antisymm (ge_of_tendsto htail hmass) zero_le

end FalconerThetaGauge
