/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.FourierReconstructionPairing
public import FalconerThetaGauge.ReconstructionDensity
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The summable finite-measure reconstruction criterion

The concrete first-norm remainder series and concrete second-norm Fourier-band series
reconstruct the source on Schwartz functions. This gives the absolute-continuity criterion
of Lemma 4.2 without assuming a density or an abstract reconstruction identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter SchwartzMap FourierTransform
open scoped ENNReal Topology Classical

namespace FalconerThetaGauge

/-- Integration against a fixed Schwartz function is a continuous linear functional on `Lp`. -/
def schwartzLpPairing (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : SchwartzMap ℝ ℂ) :
    Lp ℂ p (volume : Measure ℝ) →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
    (Lp.toTemperedDistributionCLM ℂ volume p)

theorem schwartzLpPairing_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : SchwartzMap ℝ ℂ) (f : Lp ℂ p volume) :
    schwartzLpPairing p φ f = ∫ x, φ x * f x := by
  change (Lp.toTemperedDistribution f) φ = _
  rw [Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]

theorem schwartzLpPairing_schwartzMeasureL1
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K φ : SchwartzMap ℝ ℂ) :
    schwartzLpPairing 1 φ (schwartzMeasureL1 μ K) =
      ∫ x, schwartzMeasureDensity μ K x * φ x := by
  rw [schwartzLpPairing_apply]
  apply integral_congr_ae
  filter_upwards [schwartzMeasureL1_coeFn μ K] with x hx
  rw [hx, mul_comm]

theorem schwartzMeasureDensity_sub_kernel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K L : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzMeasureDensity μ (K - L) x =
      schwartzMeasureDensity μ K x - schwartzMeasureDensity μ L x := by
  exact integral_sub (integrable_schwartzMeasureDensity_integrand μ K x)
    (integrable_schwartzMeasureDensity_integrand μ L x)

theorem integrable_schwartzMeasureDensity_mul_schwartz
    (μ : Measure ℝ) [IsFiniteMeasure μ] (K φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x ↦ schwartzMeasureDensity μ K x * φ x) volume :=
  (integrable_schwartzMeasureDensity μ K).mul_bdd φ.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ φ.norm_le_seminorm ℝ x)

theorem schwartzLpPairing_band_sub
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    schwartzLpPairing 1 φ (schwartzMeasureL1 μ (reconstructionBand n)) =
      schwartzLpPairing 1 φ (schwartzMeasureL1 μ (reconstructionLowpass (n + 1))) -
        schwartzLpPairing 1 φ (schwartzMeasureL1 μ (reconstructionLowpass n)) := by
  simp_rw [schwartzLpPairing_schwartzMeasureL1, reconstructionBand,
    schwartzMeasureDensity_sub_kernel, sub_mul]
  exact integral_sub (integrable_schwartzMeasureDensity_mul_schwartz μ _ φ)
    (integrable_schwartzMeasureDensity_mul_schwartz μ _ φ)

theorem schwartzLpPairing_band_decomposition
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hν : ν ≤ μ)
    (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    schwartzLpPairing 1 φ (schwartzMeasureL1 μ (reconstructionBand n)) =
      schwartzLpPairing 1 φ (schwartzMeasureL1 (μ - ν) (reconstructionBand n)) +
        schwartzLpPairing 2 (𝓕⁻ φ) (measureFourierBandL2 ν n) := by
  rw [schwartzLpPairing_apply 2, ← integral_measureFourierBandL2_mul_schwartz]
  simp_rw [schwartzLpPairing_schwartzMeasureL1,
    schwartzMeasureDensity_sub_measure μ ν hν, sub_mul]
  rw [integral_sub (integrable_schwartzMeasureDensity_mul_schwartz μ _ φ)
    (integrable_schwartzMeasureDensity_mul_schwartz ν _ φ)]
  exact (sub_add_cancel _ _).symm

/-- A finite measure reconstructed from dominated approximants with summable removed mass
and summable exact dyadic Fourier-shell energy is absolutely continuous.

The sequence `ν n` is the manuscript's approximant at shell index `n + N₀ + 1`.
Thus the hypotheses permit any finite initial collection of omitted shells. -/
theorem absolutelyContinuous_of_summable_dyadic_reconstruction
    (μ : Measure ℝ) [IsFiniteMeasure μ] (ν : ℕ → Measure ℝ)
    [∀ n, IsFiniteMeasure (ν n)] (N₀ : ℕ) (hν : ∀ n, ν n ≤ μ)
    (hremoved : Summable (fun n ↦ μ.real univ - (ν n).real univ))
    (henergy : Summable (fun n ↦ dyadicMeasureFourierEnergy (ν n) (n + N₀ + 1))) :
    μ ≪ volume := by
  let base : Lp ℂ 1 volume := schwartzMeasureL1 μ (reconstructionLowpass N₀)
  let error : ℕ → Lp ℂ 1 volume := fun n ↦
    schwartzMeasureL1 (μ - ν n) (reconstructionBand (n + N₀))
  let good : ℕ → Lp ℂ 2 volume := fun n ↦ measureFourierBandL2 (ν n) (n + N₀)
  have he : Summable error :=
    (summable_norm_smoothed_remainders μ ν hν (fun n ↦ reconstructionBand (n + N₀))
      (fun n ↦ integral_norm_reconstructionBand_le (n + N₀)) hremoved).of_norm
  have hg : Summable good := summable_measureFourierBandL2 ν N₀ henergy
  let f : Lp ℂ 1 volume := base + ∑' n, error n
  let g : Lp ℂ 2 volume := ∑' n, good n
  apply absolutelyContinuous_of_l1_fourier_l2_schwartz_pairing (L1.integrable_coeFn f) g
  intro φ
  have hfinite (N : ℕ) :
      schwartzLpPairing 1 φ (base + ∑ n ∈ Finset.range N, error n) +
        schwartzLpPairing 2 (𝓕⁻ φ) (∑ n ∈ Finset.range N, good n) =
      schwartzLpPairing 1 φ (schwartzMeasureL1 μ (reconstructionLowpass (N + N₀))) := by
    calc
      _ = schwartzLpPairing 1 φ base + ∑ n ∈ Finset.range N,
          (schwartzLpPairing 1 φ (error n) + schwartzLpPairing 2 (𝓕⁻ φ) (good n)) := by
        rw [map_add, map_sum, map_sum, add_assoc, Finset.sum_add_distrib]
      _ = schwartzLpPairing 1 φ base + ∑ n ∈ Finset.range N,
          schwartzLpPairing 1 φ (schwartzMeasureL1 μ (reconstructionBand (n + N₀))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        exact (schwartzLpPairing_band_decomposition μ (ν n) (hν n) (n + N₀) φ).symm
      _ = schwartzLpPairing 1 φ base + ∑ n ∈ Finset.range N,
          (schwartzLpPairing 1 φ (schwartzMeasureL1 μ
            (reconstructionLowpass (n + N₀ + 1))) -
            schwartzLpPairing 1 φ (schwartzMeasureL1 μ
              (reconstructionLowpass (n + N₀)))) := by
        simp_rw [schwartzLpPairing_band_sub]
      _ = _ := by
        have ht := Finset.sum_range_sub
          (fun n ↦ schwartzLpPairing 1 φ
            (schwartzMeasureL1 μ (reconstructionLowpass (n + N₀)))) N
        simp only [Nat.add_right_comm, Nat.zero_add] at ht
        rw [ht]
        exact add_sub_cancel _ _
  have hlimit : Tendsto (fun N ↦
      schwartzLpPairing 1 φ (base + ∑ n ∈ Finset.range N, error n) +
        schwartzLpPairing 2 (𝓕⁻ φ) (∑ n ∈ Finset.range N, good n))
      atTop (𝓝 (schwartzLpPairing 1 φ f + schwartzLpPairing 2 (𝓕⁻ φ) g)) :=
    ((schwartzLpPairing 1 φ).continuous.tendsto _).comp
      (tendsto_const_nhds.add he.hasSum.tendsto_sum_nat) |>.add
        (((schwartzLpPairing 2 (𝓕⁻ φ)).continuous.tendsto _).comp
          hg.hasSum.tendsto_sum_nat)
  have hsource : Tendsto (fun N ↦
      schwartzLpPairing 1 φ (schwartzMeasureL1 μ (reconstructionLowpass (N + N₀))))
      atTop (𝓝 (∫ x, φ x ∂μ)) := by
    simp_rw [schwartzLpPairing_schwartzMeasureL1]
    exact (tendsto_integral_reconstructionLowpass_schwartz μ φ).comp
      (tendsto_add_atTop_nat N₀)
  have hid := tendsto_nhds_unique hsource (hlimit.congr hfinite)
  simpa only [schwartzLpPairing_apply] using hid

/-- Lemma 4.2 in its original tail-indexed form: finitely many initial shells may be
ignored, and domination supplies finiteness of every approximant that is used. -/
theorem summable_reconstruction
    (μ : Measure ℝ) [IsFiniteMeasure μ] (τ : ℕ → Measure ℝ) (N₀ : ℕ)
    (hτ : ∀ N, N₀ ≤ N → τ N ≤ μ)
    (hremoved : Summable (fun n ↦ μ.real univ - (τ (n + N₀)).real univ))
    (henergy : Summable (fun n ↦ dyadicMeasureFourierEnergy (τ (n + N₀)) (n + N₀))) :
    μ ≪ volume := by
  let ν : ℕ → Measure ℝ := fun n ↦ τ (n + N₀ + 1)
  have hν : ∀ n, ν n ≤ μ := fun n ↦ hτ (n + N₀ + 1) (by omega)
  let : ∀ n, IsFiniteMeasure (ν n) := fun n ↦ isFiniteMeasure_of_le μ (hν n)
  apply absolutelyContinuous_of_summable_dyadic_reconstruction μ ν N₀ hν
  · have h := (summable_nat_add_iff (f := fun n ↦
        μ.real univ - (τ (n + N₀)).real univ) 1).mpr hremoved
    simpa only [ν, Nat.add_right_comm] using h
  · have h := (summable_nat_add_iff (f := fun n ↦
        dyadicMeasureFourierEnergy (τ (n + N₀)) (n + N₀)) 1).mpr henergy
    simpa only [ν, Nat.add_right_comm] using h

end FalconerThetaGauge
