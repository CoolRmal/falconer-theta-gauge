module

public import FalconerThetaGauge.FourierSeparationKernel
public import FalconerThetaGauge.MaskedMattilaSymbolRegularity
public import FalconerThetaGauge.StationaryCircularSource
public import FalconerThetaGauge.DirectionalTestsAverageBands

/-! # Actual circular pair kernels and their genuine stationary-phase expansion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff ComplexConjugate RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman

/-- The actual angular integral `I_x(r)` in the far terms of source Estimate 7.8. -/
def spaceSplittingCircleIntegral (b : Plane → UnitCircle → ℝ) (r : ℝ)
    (x x' : Plane) : ℂ :=
  ∫ w, maskedFourierPairKernel b b r w (x, x') ∂circleArcLength

theorem norm_spaceSplittingCircleIntegral_le {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hbound : ∀ x w, |b x w| ≤ 1)
    (r : ℝ) (x x' : Plane) : ‖spaceSplittingCircleIntegral b r x x'‖ ≤ 2 * Real.pi := by
  have hi : Integrable (fun w ↦ maskedFourierPairKernel b b r w (x, x'))
      circleArcLength := by
    apply (integrable_const (1 : ℝ)).mono
    · exact ((measurable_maskedFourierPairKernel hb hb r).of_uncurry_right).aestronglyMeasurable
    · filter_upwards [] with w
      rw [norm_maskedFourierPairKernel, norm_one]
      simpa only [one_mul] using
        mul_le_mul (hbound x w) (hbound x' w) (abs_nonneg _) (by norm_num)
  unfold spaceSplittingCircleIntegral
  calc
    _ ≤ ∫ w, ‖maskedFourierPairKernel b b r w (x, x')‖ ∂circleArcLength :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _w, (1 : ℝ) ∂circleArcLength := by
      apply integral_mono hi.norm (integrable_const (1 : ℝ))
      intro w
      dsimp only
      rw [norm_maskedFourierPairKernel]
      simpa only [one_mul] using
        mul_le_mul (hbound x w) (hbound x' w) (abs_nonneg _) (by norm_num)
    _ = _ := by simp [measureReal_def, circleArcLength_univ, Real.pi_pos.le]

/-- Angular Fubini retains the genuine circle spectrum and the genuine spatial pair measure. -/
theorem integral_spaceSplittingCircleIntegral (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (r : ℝ) :
    (∫ p, spaceSplittingCircleIntegral b r p.1 p.2 ∂(ρ.restrict X).prod (ρ.restrict X)) =
      ((∫ w, ‖maskedFourierAmplitude ρ X b r w‖ ^ (2 : ℕ)
        ∂circleArcLength : ℝ) : ℂ) := by
  have h := integral_spatial_circle_maskedFourierPairKernel ρ ρ X X hb hb hbound hbound
    (ψ := fun _ ↦ 1) measurable_const (fun _ ↦ by norm_num) r
  simp only [Complex.ofReal_one, one_mul, Complex.star_def, Complex.mul_conj'] at h
  simpa only [spaceSplittingCircleIntegral, ← Complex.ofReal_pow,
    integral_complex_ofReal] using h

/-- The exact arc-length convention gives the literal full-circle interval integral. -/
theorem spaceSplittingCircleIntegral_eq_interval {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (r : ℝ) (x x' : Plane) :
    spaceSplittingCircleIntegral b r x x' =
      ∫ θ in -Real.pi..Real.pi,
        Complex.exp (-((r * inner ℝ (x - x') (angularDirection θ) : ℝ) : ℂ) * Complex.I) *
          builtSymbolPairAngularAmplitude b b x x' θ := by
  unfold spaceSplittingCircleIntegral circleArcLength
  rw [integral_map_of_stronglyMeasurable continuous_unitCircleOfAngle.measurable
    ((measurable_maskedFourierPairKernel hb hb r).of_uncurry_right.stronglyMeasurable)]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp only [radialAngularMeasure, maskedFourierPairKernel, builtSymbolPairAngularAmplitude,
    builtSymbolAngularAmplitude, Pi.mul_apply, coe_unitCircleOfAngle, mul_assoc]

/-- The full-circle stationary formula applies to the actual source built symbols at two pins. -/
theorem spaceSplittingCircleIntegral_stationary {ρ : Measure Plane} {T : ℕ}
    (hT : 1 ≤ T) {E width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E width (8 * T) I (2 * T))
    {r : ℝ} {x x' : Plane} (hΛ : 1 ≤ r * dist x x') :
    ‖spaceSplittingCircleIntegral b r x x' -
      (Real.sqrt (2 * Real.pi / (r * dist x x')) : ℂ) *
        (Complex.exp (-((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
            stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
              (radialAngle 0 (x - x')) +
        Complex.exp (((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
            stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
              (radialAngle 0 (x - x') + Real.pi))‖ ≤
      Real.sqrt (2 * Real.pi / (r * dist x x')) *
        circularStationaryRemainderBase T (2 * max 1 (scheduledSymbolScale T E I L)) *
        (circularStationaryRemainderBase T (2 * max 1 (scheduledSymbolScale T E I L)) /
          (r * dist x x')) ^ T := by
  have hz : x - x' ≠ 0 := by
    intro hz
    have hdist : dist x x' = 0 := by simp [dist_eq_norm, hz]
    rw [hdist, mul_zero] at hΛ
    linarith
  have hreg := builtSymbolPairAngularAmplitude_isDerivativeRegular hL hL hb hb x x'
  have hreg' := hreg.of_le (show 2 * T + 2 ≤ 6 * T by omega)
  have h := circular_stationary_phase (φ := radialAngle 0 (x - x')) hreg'
    (contDiff_builtSymbolPairAngularAmplitude hb hb x x')
    (periodic_builtSymbolPairAngularAmplitude b b x x') hΛ (-Real.pi)
  have hm : Measurable (uncurry b) := by
    obtain ⟨d, _, rfl⟩ := hb
    exact d.measurable_symbol ρ E width (8 * T) I
  rw [spaceSplittingCircleIntegral_eq_interval hm]
  have heq : (fun θ ↦ Complex.exp
      (-((r * inner ℝ (x - x') (angularDirection θ) : ℝ) : ℂ) * Complex.I) *
        builtSymbolPairAngularAmplitude b b x x' θ) =
      (fun θ ↦ Complex.exp
        (-((r * dist x x' * Real.cos (θ - radialAngle 0 (x - x')) : ℝ) : ℂ) * Complex.I) *
          builtSymbolPairAngularAmplitude b b x x' θ) := by
    funext θ
    rw [inner_vector_angularDirection_eq (x - x') hz θ, dist_eq_norm]
    congr 2
    push_cast
    ring
  rw [heq]
  simpa only [neg_add_cancel, show -Real.pi + 2 * Real.pi = Real.pi by ring,
    ← two_mul, one_mul] using h

end FalconerThetaGauge
