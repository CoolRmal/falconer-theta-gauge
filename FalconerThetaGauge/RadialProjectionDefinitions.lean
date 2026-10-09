module

public import FalconerThetaGauge.Statement
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Actual radial directions, arc length, and projection kernels

The target circle is the Euclidean unit sphere. The radial projection from `x`
points toward `y`, as in Theorem 5.4. On the diagonal it is assigned the unit
direction of angle zero. Arc length is the pushforward of Lebesgue measure on
the single-turn interval `(-π, π]`, so its total mass is `2π`.

The complex coordinate and kernel construction are adapted from
`FalconerPacking.PolarFourierEnergy` and `FalconerPacking.RadialProjectionKernel`
(original source credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace FalconerThetaGauge

/-- The actual Euclidean unit circle. -/
abbrev UnitCircle := Metric.sphere (0 : Plane) 1

/-- The unit vector of angle `θ` in the standard Euclidean orientation. -/
def angularDirection (θ : ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr (Real.cos θ + Real.sin θ * Complex.I)

@[simp]
theorem norm_angularDirection (θ : ℝ) : ‖angularDirection θ‖ = 1 := by
  rw [angularDirection, LinearIsometryEquiv.norm_map]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I θ

@[fun_prop]
theorem continuous_angularDirection : Continuous angularDirection := by
  unfold angularDirection
  fun_prop

/-- The unit-circle point of angle `θ`. -/
def unitCircleOfAngle (θ : ℝ) : UnitCircle :=
  ⟨angularDirection θ, by simp⟩

@[simp]
theorem coe_unitCircleOfAngle (θ : ℝ) : (unitCircleOfAngle θ : Plane) = angularDirection θ := rfl

@[fun_prop]
theorem continuous_unitCircleOfAngle : Continuous unitCircleOfAngle := by
  unfold unitCircleOfAngle
  fun_prop

/-- The angle from the pin `x` toward the source point `y`; its diagonal value is zero. -/
def radialAngle (x y : Plane) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm (y - x))

@[fun_prop]
theorem measurable_radialAngle : Measurable (Function.uncurry radialAngle) := by
  unfold Function.uncurry radialAngle
  fun_prop

theorem radialAngle_mem (x y : Plane) : radialAngle x y ∈ Ioc (-Real.pi) Real.pi :=
  ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

@[simp]
theorem radialAngle_self (x : Plane) : radialAngle x x = 0 := by simp [radialAngle]

theorem angularDirection_radialAngle {x y : Plane} (hxy : x ≠ y) :
    angularDirection (radialAngle x y) = ‖y - x‖⁻¹ • (y - x) := by
  have h := congrArg Complex.orthonormalBasisOneI.repr
    (Complex.norm_mul_cos_add_sin_mul_I
      (Complex.orthonormalBasisOneI.repr.symm (y - x)))
  have hnorm : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have he : ‖y - x‖ • angularDirection (radialAngle x y) = y - x := by
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.real_smul,
      map_smul, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.apply_symm_apply,
      angularDirection, radialAngle] using h
  simpa only [smul_smul, inv_mul_cancel₀ hnorm, one_smul] using
    congrArg (fun v ↦ ‖y - x‖⁻¹ • v) he

/-- The actual unit-circle radial projection `π_x(y)`, defined also on the diagonal. -/
def radialProjection (x y : Plane) : UnitCircle := unitCircleOfAngle (radialAngle x y)

@[simp]
theorem radialProjection_self (x : Plane) : radialProjection x x = unitCircleOfAngle 0 := by
  simp [radialProjection]

theorem coe_radialProjection_of_ne {x y : Plane} (hxy : x ≠ y) :
    (radialProjection x y : Plane) = ‖y - x‖⁻¹ • (y - x) :=
  angularDirection_radialAngle hxy

@[fun_prop]
theorem measurable_radialProjection : Measurable (Function.uncurry radialProjection) := by
  exact continuous_unitCircleOfAngle.measurable.comp measurable_radialAngle

/-- The manuscript's pair direction `e(x,y)`, pointing from `y` toward `x`. -/
def pairDirection (x y : Plane) : UnitCircle := radialProjection y x

theorem coe_pairDirection_of_ne {x y : Plane} (hxy : x ≠ y) :
    (pairDirection x y : Plane) = ‖x - y‖⁻¹ • (x - y) :=
  coe_radialProjection_of_ne (Ne.symm hxy)

/-- Lebesgue angular measure over one full turn, without probability normalization. -/
def radialAngularMeasure : Measure ℝ := volume.restrict (Ioc (-Real.pi) Real.pi)

instance : IsFiniteMeasure radialAngularMeasure := by
  unfold radialAngularMeasure
  infer_instance

/-- Actual circle arc length, with total mass `2π`. -/
def circleArcLength : Measure UnitCircle := radialAngularMeasure.map unitCircleOfAngle

instance : IsFiniteMeasure circleArcLength := by
  unfold circleArcLength
  infer_instance

theorem circleArcLength_univ : circleArcLength univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [circleArcLength, Measure.map_apply continuous_unitCircleOfAngle.measurable
    MeasurableSet.univ, preimage_univ, radialAngularMeasure, Measure.restrict_apply_univ,
    Real.volume_Ioc]
  congr 1
  ring

/-- The actual radial pushforward at each pin is a jointly measurable probability kernel. -/
def radialProjectionKernel (μ : Measure Plane) [SFinite μ] : Kernel Plane UnitCircle where
  toFun x := μ.map (radialProjection x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.map_apply measurable_radialProjection.of_uncurry_left hS]
    exact measurable_measure_prodMk_left (measurable_radialProjection hS)

@[simp]
theorem radialProjectionKernel_apply (μ : Measure Plane) [SFinite μ] (x : Plane) :
    radialProjectionKernel μ x = μ.map (radialProjection x) := rfl

instance (μ : Measure Plane) [IsFiniteMeasure μ] : IsFiniteKernel (radialProjectionKernel μ) := by
  refine ⟨μ univ, measure_lt_top _ _, fun x ↦ ?_⟩
  simp [Measure.map_apply measurable_radialProjection.of_uncurry_left]

instance (μ : Measure Plane) [IsProbabilityMeasure μ] : IsMarkovKernel (radialProjectionKernel μ) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (μ.map (radialProjection x))
    infer_instance

/-- The Borel Radon--Nikodym density of the absolutely continuous part, jointly in pin/direction.
Theorem 5.4's absolute-continuity assertion remains an independent analytic obligation. -/
def radialProjectionDensity (μ : Measure Plane) [SFinite μ] (x : Plane) (w : UnitCircle) : ℝ≥0∞ :=
  Kernel.rnDeriv (radialProjectionKernel μ) (Kernel.const Plane circleArcLength) x w

@[fun_prop]
theorem measurable_radialProjectionDensity (μ : Measure Plane) [SFinite μ] :
    Measurable (Function.uncurry (radialProjectionDensity μ)) := by
  exact Kernel.measurable_rnDeriv _ _

end FalconerThetaGauge
