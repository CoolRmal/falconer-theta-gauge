module

public import FalconerThetaGauge.RadialProjectionLimitJoint

/-!
# Weak convergence through separated radial projections

Restriction to a common closed carrier turns continuity on that carrier into
ordinary continuity on a subtype. The resulting weak convergence of the
actual radial joint distributions uses the concrete separation of the pin
and source carriers, so the specified diagonal value has no effect.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- A measurable map continuous on a common closed carrier preserves weak
convergence of the actual probability measures. -/
theorem tendsto_probabilityMeasure_map_of_continuousOn_closed
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace α] [TopologicalSpace β] [BorelSpace α] [BorelSpace β]
    [NormalSpace α] {σ : ProbabilityMeasure α} {σn : ℕ → ProbabilityMeasure α}
    (hconv : Tendsto σn atTop (𝓝 σ)) {K : Set α} (hK : IsClosed K)
    (hσ : (σ : Measure α) Kᶜ = 0) (hσn : ∀ n, (σn n : Measure α) Kᶜ = 0)
    {f : α → β} (hf : Measurable f) (hcont : ContinuousOn f K) :
    Tendsto (fun n ↦ (σn n).map f) atTop (𝓝 (σ.map f)) := by
  let e : K → α := Subtype.val
  have he : Topology.IsClosedEmbedding e := hK.isClosedEmbedding_subtypeVal
  have hfin : Tendsto (fun n ↦ (σn n).toFiniteMeasure) atTop (𝓝 σ.toFiniteMeasure) :=
    ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp hconv
  have hmem : σ.toFiniteMeasure ∈ {τ : FiniteMeasure α | τ (range e)ᶜ = 0} := by
    change σ.toFiniteMeasure (range e)ᶜ = 0
    rw [FiniteMeasure.null_iff_toMeasure_null]
    simpa only [e, Subtype.range_coe,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using hσ
  have hwithin : Tendsto (fun n ↦ (σn n).toFiniteMeasure) atTop
      (𝓝[{τ : FiniteMeasure α | τ (range e)ᶜ = 0}] σ.toFiniteMeasure) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hfin, Eventually.of_forall ?_⟩
    intro n
    change (σn n).toFiniteMeasure (range e)ᶜ = 0
    rw [FiniteMeasure.null_iff_toMeasure_null]
    simpa only [e, Subtype.range_coe,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using hσn n
  have hpull := (he.continuousOn_comap_finiteMeasure σ.toFiniteMeasure hmem).tendsto.comp hwithin
  have hmap := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n ↦ (σn n).toFiniteMeasure.comap e) (σ.toFiniteMeasure.comap e) hpull
    (hcont.domRestrict : Continuous (fun x : K ↦ f x))
  have hident (τ : ProbabilityMeasure α) (hτ : (τ : Measure α) Kᶜ = 0) :
      (τ.toFiniteMeasure.comap e).map (fun x : K ↦ f x) = (τ.map f).toFiniteMeasure := by
    apply Subtype.ext
    change ((τ : Measure α).comap e).map (f ∘ e) = (τ : Measure α).map f
    rw [← Measure.map_map hf he.continuous.measurable, he.measurableEmbedding.map_comap,
      show range e = K from Subtype.range_coe]
    rw [Measure.restrict_eq_self_of_ae_mem hτ]
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  change Tendsto (fun n ↦ ((σn n).toFiniteMeasure.comap e).map (fun x : K ↦ f x)) atTop
    (𝓝 ((σ.toFiniteMeasure.comap e).map (fun x : K ↦ f x))) at hmap
  simpa only [Function.comp_def, hident σ hσ, hident (σn _) (hσn _)] using hmap

/-- Weak convergence of sources gives weak convergence of actual pin/direction
distributions whenever their common closed carriers stay separated. -/
theorem tendsto_jointRadialProbability_of_separated
    (μ ν : ProbabilityMeasure Plane) {νn : ℕ → ProbabilityMeasure Plane}
    (hconv : Tendsto νn atTop (𝓝 ν)) {K L : Set Plane}
    (hK : IsClosed K) (hL : IsClosed L)
    (hμ : (μ : Measure Plane) Kᶜ = 0) (hν : (ν : Measure Plane) Lᶜ = 0)
    (hνn : ∀ n, (νn n : Measure Plane) Lᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ x ∈ K, ∀ y ∈ L, s ≤ dist x y) :
    Tendsto (fun n ↦ jointRadialProbability μ (νn n)) atTop
      (𝓝 (jointRadialProbability μ ν)) := by
  have hprod : Tendsto (fun n ↦ μ.prod (νn n)) atTop (𝓝 (μ.prod ν)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (tendsto_const_nhds.prodMk_nhds hconv)
  have hsupport (τ : ProbabilityMeasure Plane) (hτ : (τ : Measure Plane) Lᶜ = 0) :
      ((μ.prod τ : ProbabilityMeasure (Plane × Plane)) : Measure (Plane × Plane))
        (K ×ˢ L)ᶜ = 0 := by
    have hmem : ∀ᵐ p ∂(μ : Measure Plane).prod (τ : Measure Plane), p ∈ K ×ˢ L := by
      apply (Measure.ae_prod_mem_iff_ae_ae_mem (hK.measurableSet.prod hL.measurableSet)).mpr
      filter_upwards [ae_iff.mpr hμ] with x hx
      filter_upwards [ae_iff.mpr hτ] with y hy
      exact ⟨hx, hy⟩
    exact ae_iff.mp hmem
  have hcont : ContinuousOn jointRadialMap (K ×ˢ L) :=
    continuous_fst.continuousOn.prodMk
      (continuousOn_radialProjection_of_separated hs hsep)
  have h := tendsto_probabilityMeasure_map_of_continuousOn_closed hprod (hK.prod hL)
    (hsupport ν hν) (fun n ↦ hsupport (νn n) (hνn n)) measurable_jointRadialMap hcont
  exact h

end FalconerThetaGauge
