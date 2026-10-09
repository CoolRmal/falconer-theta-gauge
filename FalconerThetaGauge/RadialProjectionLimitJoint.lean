module

public import FalconerThetaGauge.RadialProjectionLimitOrlicz
public import FalconerThetaGauge.RadialProjectionRay
public import FalconerThetaGauge.RadialProjectionContinuity
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# The actual joint radial measure

The pin/source product is pushed forward by `(x,y) ↦ (x,πₓ(y))`. It equals
the composition-product with the actual radial kernel. For a source density,
its joint density against pin measure times circle arc length is the genuine
polar ray integral. The joint Radon–Nikodym derivative agrees almost everywhere
with the previously defined kernel density.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The genuine joint radial map retains the pin and projects the source onto the circle. -/
def jointRadialMap (p : Plane × Plane) : Plane × UnitCircle :=
  (p.1, radialProjection p.1 p.2)

@[fun_prop]
theorem measurable_jointRadialMap : Measurable jointRadialMap :=
  measurable_fst.prodMk measurable_radialProjection

/-- The actual joint distribution of the pin and radial source direction. -/
def jointRadialMeasure (μ ν : Measure Plane) : Measure (Plane × UnitCircle) :=
  (μ.prod ν).map jointRadialMap

theorem jointRadialMeasure_eq_compProd (μ ν : Measure Plane) [SFinite μ] [IsFiniteMeasure ν] :
    jointRadialMeasure μ ν = μ ⊗ₘ radialProjectionKernel ν := by
  ext S hS
  rw [jointRadialMeasure, Measure.map_apply measurable_jointRadialMap hS,
    Measure.prod_apply (measurable_jointRadialMap hS), Measure.compProd_apply hS]
  congr with x
  rw [radialProjectionKernel_apply,
    Measure.map_apply measurable_radialProjection.of_uncurry_left (measurable_prodMk_left hS)]
  rfl

instance (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (jointRadialMeasure μ ν) := by
  unfold jointRadialMeasure
  infer_instance

/-- Probability-valued version of the same actual joint distribution. -/
def jointRadialProbability (μ ν : ProbabilityMeasure Plane) : ProbabilityMeasure (Plane × UnitCircle) :=
  ⟨jointRadialMeasure μ ν, inferInstance⟩

@[simp]
theorem coe_jointRadialProbability (μ ν : ProbabilityMeasure Plane) :
    (jointRadialProbability μ ν : Measure (Plane × UnitCircle)) = jointRadialMeasure μ ν := rfl

/-- A genuine source density has exactly its polar ray integral as joint radial density. -/
theorem jointRadialMeasure_withDensity_eq (μ : Measure Plane) [SFinite μ]
    {f : Plane → ℝ≥0∞} (hf : Measurable f) [IsFiniteMeasure (volume.withDensity f)] :
    jointRadialMeasure μ (volume.withDensity f) =
      (μ.prod circleArcLength).withDensity (fun p ↦ circleRayDensity f p.1 p.2) := by
  let κ : Kernel Plane UnitCircle :=
    (Kernel.const Plane circleArcLength).withDensity (circleRayDensity f)
  have hκ : κ = radialProjectionKernel (volume.withDensity f) := by
    ext x S hS
    dsimp only [κ]
    rw [Kernel.withDensity_apply _ (measurable_circleRayDensity hf)]
    change circleArcLength.withDensity (circleRayDensity f x) S =
      ((volume.withDensity f).map (radialProjection x)) S
    rw [map_radialProjection_withDensity_eq hf x]
  have : IsSFiniteKernel κ := hκ ▸ inferInstance
  rw [jointRadialMeasure_eq_compProd, ← hκ]
  change μ ⊗ₘ (Kernel.const Plane circleArcLength).withDensity (circleRayDensity f) = _
  rw [Measure.compProd_withDensity (measurable_circleRayDensity hf), Measure.compProd_const]

/-- The actual joint derivative equals the actual radial kernel derivative almost everywhere. -/
theorem jointRadialMeasure_rnDeriv_ae_eq (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (jointRadialMeasure μ ν).rnDeriv (μ.prod circleArcLength) =ᵐ[μ.prod circleArcLength]
      fun p ↦ radialProjectionDensity ν p.1 p.2 := by
  rw [jointRadialMeasure_eq_compProd, ← Measure.compProd_const]
  exact ProbabilityTheory.rnDeriv_measure_compProd_right μ (radialProjectionKernel ν)
    (Kernel.const Plane circleArcLength)

end FalconerThetaGauge
