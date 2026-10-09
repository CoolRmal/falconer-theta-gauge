module

public import FalconerThetaGauge.SpaceSplittingCaseAFactor
public import FalconerThetaGauge.SpaceSplittingCircleRemainder

/-! # Genuine radial and circle Fubini in Case A -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace FalconerThetaGauge

def spaceSplittingCaseAProductIntegrand (K v j : ℕ) (σ d : ℝ)
    (b : Plane → UnitCircle → ℝ) (y y' : Plane) (q : ℝ × UnitCircle) : ℂ :=
  Complex.exp (-((q.1 * (σ * d) : ℝ) : ℂ) * Complex.I) *
    spaceSplittingCaseAAmplitude K v j q.1 * maskedFourierPairKernel b b q.1 q.2 (y, y')

theorem integrable_spaceSplittingCaseAProductIntegrand (K v j : ℕ) (σ d : ℝ)
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (y y' : Plane) :
    Integrable (spaceSplittingCaseAProductIntegrand K v j σ d b y y')
      (volume.prod circleArcLength) := by
  have hA : Integrable (spaceSplittingCaseAAmplitude K v j) :=
    (contDiff_spaceSplittingRealPowerAmplitude K v _).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_spaceSplittingRealPowerAmplitude K v _)
  have hm : Measurable (spaceSplittingCaseAProductIntegrand K v j σ d b y y') := by
    have hby : Measurable (fun q : ℝ × UnitCircle ↦ b y q.2) :=
      hb.comp (measurable_const.prodMk measurable_snd)
    have hby' : Measurable (fun q : ℝ × UnitCircle ↦ b y' q.2) :=
      hb.comp (measurable_const.prodMk measurable_snd)
    unfold spaceSplittingCaseAProductIntegrand maskedFourierPairKernel
    have harg : Measurable (fun q : ℝ × UnitCircle ↦ Complex.exp
        (-((q.1 * inner ℝ (y - y') (q.2 : Plane) : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact ((by fun_prop : Measurable (fun q : ℝ × UnitCircle ↦
      Complex.exp (-((q.1 * (σ * d) : ℝ) : ℂ) * Complex.I))).mul
      ((contDiff_spaceSplittingRealPowerAmplitude K v _).continuous.measurable.comp
        measurable_fst)).mul ((harg.mul hby.complex_ofReal).mul hby'.complex_ofReal)
  apply (hA.norm.mul_prod (integrable_const (1 : ℝ) (μ := circleArcLength))).mono
    hm.aestronglyMeasurable
  filter_upwards [] with q
  have he : ‖Complex.exp (-((q.1 * (σ * d) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [spaceSplittingCaseAProductIntegrand, norm_mul, he, one_mul,
    norm_maskedFourierPairKernel, norm_norm, mul_one]
  have hh := mul_le_mul (hbound y q.2) (hbound y' q.2) (abs_nonneg _) (by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
    (norm_nonneg (spaceSplittingCaseAAmplitude K v j q.1))

theorem integral_spaceSplittingCaseAAmplitude_circle_eq (K v j : ℕ) (σ d : ℝ)
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hbound : ∀ x w, |b x w| ≤ 1) (y y' : Plane) :
    (∫ r : ℝ, Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I) *
      spaceSplittingCaseAAmplitude K v j r * spaceSplittingCircleIntegral b r y y') =
      ∫ w, (b y w : ℂ) * (b y' w : ℂ) *
        spaceSplittingCaseARadialMoment K v j
          (σ * d + inner ℝ (w : Plane) (y - y')) ∂circleArcLength := by
  have hi := integrable_spaceSplittingCaseAProductIntegrand K v j σ d hb hbound y y'
  calc
    _ = ∫ r : ℝ, ∫ w, spaceSplittingCaseAProductIntegrand K v j σ d b y y' (r, w)
        ∂circleArcLength := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [spaceSplittingCircleIntegral, ← integral_const_mul]
      rfl
    _ = ∫ w, (∫ r : ℝ, spaceSplittingCaseAProductIntegrand K v j σ d b y y' (r, w))
        ∂circleArcLength := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [spaceSplittingCaseARadialMoment, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with r
      have he : Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((r * inner ℝ (y - y') (w : Plane) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (-((r * (σ * d + inner ℝ (w : Plane) (y - y')) : ℝ) : ℂ) *
            Complex.I) := by
        rw [← Complex.exp_add, real_inner_comm (y - y') (w : Plane)]
        congr 1
        push_cast
        ring
      dsimp only [spaceSplittingCaseAProductIntegrand, maskedFourierPairKernel]
      calc
        _ = (b y w : ℂ) * (b y' w : ℂ) *
            (Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-((r * inner ℝ (y - y') (w : Plane) : ℝ) : ℂ) * Complex.I)) *
              spaceSplittingCaseAAmplitude K v j r := by ring
        _ = _ := by rw [he]; ring

theorem integrable_spaceSplittingCaseAStationaryTerm_circle (K v j : ℕ) (σ d : ℝ)
    (c : ℂ) (hd : 0 < d) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hbound : ∀ x w, |b x w| ≤ 1) (y y' : Plane) :
    Integrable (fun r : ℝ ↦ spaceSplittingCaseAStationaryTerm K v j σ d c r *
      spaceSplittingCircleIntegral b r y y') := by
  have hprod := integrable_spaceSplittingCaseAProductIntegrand K v j σ d hb hbound y y'
  have hi := hprod.integral_prod_left
  have hi' : Integrable (fun r : ℝ ↦
      Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I) *
        spaceSplittingCaseAAmplitude K v j r * spaceSplittingCircleIntegral b r y y') := by
    convert hi using 1
    funext r
    rw [spaceSplittingCircleIntegral, ← integral_const_mul]
    rfl
  convert hi'.const_mul ((Real.sqrt (2 * Real.pi / d) : ℂ) * (d : ℂ)⁻¹ ^ j * c *
    Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I)) using 1
  funext r
  rw [spaceSplittingCaseAStationaryTerm_eq_realPower K v j σ d c hd r]
  ring

theorem integral_spaceSplittingCaseAStationaryTerm_circle_eq (K v j : ℕ) (σ d : ℝ)
    (c : ℂ) (hd : 0 < d) {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hbound : ∀ x w, |b x w| ≤ 1) (y y' : Plane) :
    (∫ r : ℝ, spaceSplittingCaseAStationaryTerm K v j σ d c r *
      spaceSplittingCircleIntegral b r y y') =
      ∫ w, (b y w : ℂ) * (b y' w : ℂ) *
        Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
        ((Real.sqrt (2 * Real.pi / d) : ℂ) * (d : ℂ)⁻¹ ^ j * c *
          spaceSplittingCaseARadialMoment K v j
            (σ * d + inner ℝ (w : Plane) (y - y'))) ∂circleArcLength := by
  calc
    _ = ((Real.sqrt (2 * Real.pi / d) : ℂ) * (d : ℂ)⁻¹ ^ j * c *
        Complex.exp (((σ * Real.pi / 4 : ℝ) : ℂ) * Complex.I)) *
        ∫ r : ℝ, Complex.exp (-((r * (σ * d) : ℝ) : ℂ) * Complex.I) *
          spaceSplittingCaseAAmplitude K v j r * spaceSplittingCircleIntegral b r y y' := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with r
      rw [spaceSplittingCaseAStationaryTerm_eq_realPower K v j σ d c hd r]
      ring
    _ = _ := by
      rw [integral_spaceSplittingCaseAAmplitude_circle_eq K v j σ d hb hbound y y',
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      ring

end FalconerThetaGauge
