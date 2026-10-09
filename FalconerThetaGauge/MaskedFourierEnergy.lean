module

public import FalconerThetaGauge.DirectionalTestsFilter
public import FalconerThetaGauge.ScalarEnergyBinningFourier

/-!
# The actual masked Fourier amplitude and circular spectrum

These are the literal angular-frequency quantities `U_X` and `σ_X` in
Definition 7.1, for an actual carrier and a jointly Borel bounded symbol.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

/-- The literal masked Fourier amplitude of the actual carrier restriction. -/
def maskedFourierAmplitude (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℝ) (r : ℝ) (w : UnitCircle) : ℂ :=
  ∫ x in X, Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) * (b x w : ℂ) ∂ρ

/-- The actual circular Fourier spectrum per unit mass of Definition 7.1. -/
def maskedCircularSpectrum (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℝ) (r : ℝ) : ℝ :=
  r / ρ.real X * ∫ w, ‖maskedFourierAmplitude ρ X b r w‖ ^ (2 : ℕ) ∂circleArcLength

@[fun_prop]
theorem measurable_maskedFourierAmplitude (ρ : Measure Plane) [SFinite ρ] (X : Set Plane)
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b)) :
    Measurable (uncurry (maskedFourierAmplitude ρ X b)) := by
  have hm : Measurable (fun p : (ℝ × UnitCircle) × Plane ↦
      Complex.exp (-((p.1.1 * inner ℝ p.2 (p.1.2 : Plane) : ℝ) : ℂ) * Complex.I) *
        (b p.2 p.1.2 : ℂ)) := by
    have harg : Measurable (fun p : (ℝ × UnitCircle) × Plane ↦ (p.2, p.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hb' : Measurable (fun p : (ℝ × UnitCircle) × Plane ↦ b p.2 p.1.2) := hb.comp harg
    have hp : Measurable (fun p : (ℝ × UnitCircle) × Plane ↦
        Complex.exp (-((p.1.1 * inner ℝ p.2 (p.1.2 : Plane) : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    exact hp.mul hb'.complex_ofReal
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem norm_maskedFourier_integrand (b : Plane → UnitCircle → ℝ)
    (r : ℝ) (w : UnitCircle) (x : Plane) :
    ‖Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) * (b x w : ℂ)‖ =
      |b x w| := by
  rw [norm_mul, Complex.norm_exp]
  simp

theorem integrable_maskedFourier_integrand (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) (w : UnitCircle) :
    Integrable (fun x ↦
      Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) * (b x w : ℂ))
      (ρ.restrict X) := by
  apply (integrable_const (1 : ℝ)).mono ?_ ?_
  · have hbw : Measurable (fun x ↦ b x w) := hb.of_uncurry_right
    exact ((by fun_prop : Measurable (fun x : Plane ↦
      Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I))).mul
      hbw.complex_ofReal).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [norm_maskedFourier_integrand, norm_one] using hb₁ x w

/-- The true amplitude is bounded by the actual carrier mass. -/
theorem norm_maskedFourierAmplitude_le_mass (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) (w : UnitCircle) :
    ‖maskedFourierAmplitude ρ X b r w‖ ≤ ρ.real X := by
  unfold maskedFourierAmplitude
  calc
    _ ≤ ∫ x in X,
        ‖Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) * (b x w : ℂ)‖ ∂ρ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _x in X, (1 : ℝ) ∂ρ := by
      apply integral_mono (integrable_maskedFourier_integrand ρ X hb hb₁ r w).norm
        (integrable_const (1 : ℝ))
      intro x
      dsimp only
      rw [norm_maskedFourier_integrand]
      exact hb₁ x w
    _ = _ := by simp

theorem integrable_maskedFourier_circle_sq (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) (r : ℝ) :
    Integrable (fun w ↦ ‖maskedFourierAmplitude ρ X b r w‖ ^ (2 : ℕ)) circleArcLength := by
  apply (integrable_const (ρ.real X ^ (2 : ℕ))).mono ?_ ?_
  · have hm : Measurable (fun w ↦ ‖maskedFourierAmplitude ρ X b r w‖ ^ (2 : ℕ)) :=
      ((measurable_maskedFourierAmplitude ρ X hb).of_uncurry_left).norm.pow_const 2
    exact hm.aestronglyMeasurable
  · filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_maskedFourierAmplitude_le_mass ρ X hb hb₁ r w) 2

@[fun_prop]
theorem measurable_maskedCircularSpectrum (ρ : Measure Plane) [SFinite ρ] (X : Set Plane)
    {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b)) :
    Measurable (maskedCircularSpectrum ρ X b) := by
  have hstrong := ((measurable_maskedFourierAmplitude ρ X hb).norm.pow_const 2).stronglyMeasurable
  have hm := (hstrong.integral_prod_right' (ν := circleArcLength)).measurable
  exact (measurable_id.div_const _).mul hm

theorem maskedCircularSpectrum_nonneg (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ maskedCircularSpectrum ρ X b r :=
  mul_nonneg (div_nonneg hr measureReal_nonneg) (integral_nonneg fun _ ↦ sq_nonneg _)

/-- The literal spectrum satisfies the source's trivial mass bound. -/
theorem maskedCircularSpectrum_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {b : Plane → UnitCircle → ℝ} (hb : Measurable (uncurry b))
    (hb₁ : ∀ x w, |b x w| ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    maskedCircularSpectrum ρ X b r ≤ 2 * Real.pi * r * ρ.real X := by
  by_cases hX : ρ.real X = 0
  · simp [maskedCircularSpectrum, hX]
  have hXpos : 0 < ρ.real X := lt_of_le_of_ne measureReal_nonneg (Ne.symm hX)
  have hcircle : (∫ w, ‖maskedFourierAmplitude ρ X b r w‖ ^ (2 : ℕ) ∂circleArcLength) ≤
      2 * Real.pi * ρ.real X ^ (2 : ℕ) := by
    calc
      _ ≤ ∫ _w, ρ.real X ^ (2 : ℕ) ∂circleArcLength :=
        integral_mono (integrable_maskedFourier_circle_sq ρ X hb hb₁ r) (integrable_const _)
          fun w ↦ pow_le_pow_left₀ (norm_nonneg _)
            (norm_maskedFourierAmplitude_le_mass ρ X hb hb₁ r w) 2
      _ = _ := by
        rw [integral_const, Measure.real, circleArcLength_univ,
          ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  calc
    _ ≤ r / ρ.real X * (2 * Real.pi * ρ.real X ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcircle (div_nonneg hr hXpos.le)
    _ = _ := by field_simp

end FalconerThetaGauge
