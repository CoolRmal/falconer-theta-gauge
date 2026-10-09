module

public import FalconerThetaGauge.OrthogonalityRadialBudget
public import FalconerThetaGauge.OrthogonalityAngularSource
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # The literal cutoff circle kernels for two pairs of points -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

def orthogonalityCircleAmplitude (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) (w : UnitCircle) : ℂ :=
  (equalArcCutoff K ℓ arc w : ℂ) * (b x w : ℂ) * (b x' w : ℂ)

def orthogonalityCircleKernel (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) (r : ℝ) (w : UnitCircle) : ℂ :=
  Complex.exp (-((r * inner ℝ (x - x') (w : Plane) : ℝ) : ℂ) * Complex.I) *
    orthogonalityCircleAmplitude K ℓ arc b x x' w

theorem integral_circle_eq_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : UnitCircle → E} (hf : Measurable f) (u : ℝ) :
    (∫ w, f w ∂circleArcLength) = ∫ t in u..u + 2 * Real.pi, f (unitCircleOfAngle t) := by
  rw [circleArcLength,
    integral_map continuous_unitCircleOfAngle.measurable.aemeasurable hf.aestronglyMeasurable,
    radialAngularMeasure,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have hp : Periodic (fun t ↦ f (unitCircleOfAngle t)) (2 * Real.pi) := by
    intro t
    simp only [unitCircleOfAngle_add_two_pi]
  convert hp.intervalIntegral_add_eq (-Real.pi) u using 1
  congr 1
  ring

theorem orthogonalityCircleKernel_comp_angle (K : ℕ) (ℓ : ℝ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) (r t : ℝ) :
    orthogonalityCircleKernel K ℓ arc b x x' r (unitCircleOfAngle t) =
      Complex.exp ((orthogonalityAngularPhase r (x - x') t : ℂ) * Complex.I) *
        orthogonalityAngularAmplitude K ℓ arc b x x' t := by
  dsimp only [orthogonalityCircleKernel, orthogonalityCircleAmplitude,
    orthogonalityAngularPhase, orthogonalityAngularAmplitude,
    builtSymbolPairAngularAmplitude, builtSymbolAngularAmplitude, Pi.mul_apply]
  rw [coe_unitCircleOfAngle, real_inner_comm (x - x') (angularDirection t)]
  push_cast
  ring_nf

@[fun_prop]
theorem measurable_orthogonalityCircleAmplitude (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (x x' : Plane) :
    Measurable (orthogonalityCircleAmplitude K ℓ arc b x x') :=
  (((measurable_equalArcCutoff K hℓ arc).complex_ofReal.mul
    hb.of_uncurry_left.complex_ofReal).mul hb.of_uncurry_left.complex_ofReal)

@[fun_prop]
theorem measurable_orthogonalityCircleKernel (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (x x' : Plane) :
    Measurable (uncurry (orthogonalityCircleKernel K ℓ arc b x x')) := by
  have ha : Measurable (fun p : ℝ × UnitCircle ↦
      orthogonalityCircleAmplitude K ℓ arc b x x' p.2) :=
    (measurable_orthogonalityCircleAmplitude K hℓ arc hb x x').comp measurable_snd
  exact (show Measurable (fun p : ℝ × UnitCircle ↦
    Complex.exp (-((p.1 * inner ℝ (x - x') (p.2 : Plane) : ℝ) : ℂ) * Complex.I)) by
      fun_prop).mul ha

theorem norm_orthogonalityCircleKernel (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) (r : ℝ) (w : UnitCircle) :
    ‖orthogonalityCircleKernel K ℓ arc b x x' r w‖ =
      equalArcCutoff K ℓ arc w * |b x w| * |b x' w| := by
  have hn : ‖Complex.exp (-((r * inner ℝ (x - x') (w : Plane) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [orthogonalityCircleKernel, orthogonalityCircleAmplitude, norm_mul, hn,
    Complex.norm_real, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (equalArcCutoff_mem_Icc K hℓ arc w).1]

theorem norm_orthogonalityCircleKernel_le_one (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (arc : Fin (angularPartitionCount ℓ)) {b : Plane → UnitCircle → ℝ}
    (hb : ∀ x w, |b x w| ≤ 1) (x x' : Plane) (r : ℝ) (w : UnitCircle) :
    ‖orthogonalityCircleKernel K ℓ arc b x x' r w‖ ≤ 1 := by
  rw [norm_orthogonalityCircleKernel K hℓ]
  exact (mul_le_mul (mul_le_mul (equalArcCutoff_mem_Icc K hℓ arc w).2 (hb x w)
    (abs_nonneg _) (by norm_num)) (hb x' w) (abs_nonneg _) (by norm_num)).trans
    (by norm_num)

end FalconerThetaGauge
