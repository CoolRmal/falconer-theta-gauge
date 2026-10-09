module

public import FalconerThetaGauge.SpaceSplittingScalarKernel
public import FalconerThetaGauge.MaskedDistanceEnergyTests

/-! # Exact weighted-pushforward and Fubini identities for the space-splitting kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace FalconerThetaGauge

def spaceSplittingWeightedKernel (h : ℝ) (Z₁ Z₂ : Set (Plane × Plane))
    (p : (Plane × Plane) × (Plane × Plane)) : ℝ≥0∞ :=
  crossDistanceWeight p.1 * ENNReal.ofReal (Z₁.indicator (fun _ ↦ 1) p.1) *
    (crossDistanceWeight p.2 * ENNReal.ofReal (Z₂.indicator (fun _ ↦ 1) p.2)) *
      scalarBinningKernel h (dist p.1.1 p.1.2, dist p.2.1 p.2.2)

@[fun_prop]
theorem measurable_spaceSplittingWeightedKernel (h : ℝ) {Z₁ Z₂ : Set (Plane × Plane)}
    (hZ₁ : MeasurableSet Z₁) (hZ₂ : MeasurableSet Z₂) :
    Measurable (spaceSplittingWeightedKernel h Z₁ Z₂) := by
  unfold spaceSplittingWeightedKernel
  apply Measurable.mul
  · exact ((measurable_crossDistanceWeight.comp measurable_fst).mul
      ((measurable_const.indicator hZ₁).ennreal_ofReal.comp measurable_fst)).mul
      ((measurable_crossDistanceWeight.comp measurable_snd).mul
        ((measurable_const.indicator hZ₂).ennreal_ofReal.comp measurable_snd))
  · exact (measurable_scalarBinningKernel h).comp
      ((continuous_dist.measurable.comp measurable_fst).prodMk
        (continuous_dist.measurable.comp measurable_snd))

/-- The true singular weights and both true passing sets survive the distance pushforward. -/
theorem lintegral_spaceSplittingWeightedKernel_eq (ρ₁ ρ₂ ρ₃ ρ₄ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] [SFinite ρ₃] [SFinite ρ₄]
    (X₁ X₂ X₃ X₄ : Set Plane)
    {Z₁ Z₂ : Set (Plane × Plane)} (hZ₁ : MeasurableSet Z₁) (hZ₂ : MeasurableSet Z₂)
    (h : ℝ) :
    (∫⁻ p, spaceSplittingWeightedKernel h Z₁ Z₂ p
      ∂((ρ₁.restrict X₁).prod (ρ₂.restrict X₂)).prod
        ((ρ₃.restrict X₃).prod (ρ₄.restrict X₄))) =
      ∫⁻ p, scalarBinningKernel h p
        ∂(passingWeightedDistanceMeasure ρ₁ ρ₂ X₁ X₂ Z₁).prod
          (passingWeightedDistanceMeasure ρ₃ ρ₄ X₃ X₄ Z₂) := by
  let f := fun p ↦ crossDistanceWeight p * ENNReal.ofReal (Z₁.indicator (fun _ ↦ 1) p)
  let g := fun p ↦ crossDistanceWeight p * ENNReal.ofReal (Z₂.indicator (fun _ ↦ 1) p)
  have hf : Measurable f := measurable_crossDistanceWeight.mul
    ((measurable_const.indicator hZ₁).ennreal_ofReal)
  have hg : Measurable g := measurable_crossDistanceWeight.mul
    ((measurable_const.indicator hZ₂).ennreal_ofReal)
  have hk : Measurable (fun p : (Plane × Plane) × (Plane × Plane) ↦
      scalarBinningKernel h (Prod.map (fun q : Plane × Plane ↦ dist q.1 q.2)
        (fun q : Plane × Plane ↦ dist q.1 q.2) p)) :=
    (measurable_scalarBinningKernel h).comp
      ((continuous_dist.measurable.comp measurable_fst).prodMk
        (continuous_dist.measurable.comp measurable_snd))
  have hfg : Measurable (fun p : (Plane × Plane) × (Plane × Plane) ↦ f p.1 * g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  unfold passingWeightedDistanceMeasure filteredCrossDistanceMeasure
  rw [Measure.map_prod_map _ _ continuous_dist.measurable continuous_dist.measurable,
    lintegral_map (measurable_scalarBinningKernel h)
      (continuous_dist.measurable.prodMap continuous_dist.measurable),
    prod_withDensity hf hg,
    lintegral_withDensity_eq_lintegral_mul _ hfg hk]
  rfl

end FalconerThetaGauge
