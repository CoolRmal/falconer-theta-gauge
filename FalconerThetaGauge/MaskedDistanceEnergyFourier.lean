module

public import FalconerThetaGauge.MaskedDistanceEnergyCells

/-! # The genuine Fourier and Fubini interfaces for the weighted passing distance measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal

namespace FalconerThetaGauge

/-- The literal spatial oscillatory integrand for the passing weighted distance measure. -/
def passingDistanceFourierIntegrand (Z : Set (Plane × Plane)) (r : ℝ) (p : Plane × Plane) : ℂ :=
  Complex.exp (-((r * dist p.1 p.2 : ℝ) : ℂ) * Complex.I) *
    Complex.ofReal ((Real.sqrt (dist p.1 p.2))⁻¹) *
      Complex.ofReal (Z.indicator (fun _ ↦ (1 : ℝ)) p)

theorem toReal_crossDistanceWeight (p : Plane × Plane) :
    (crossDistanceWeight p).toReal = (Real.sqrt (dist p.1 p.2))⁻¹ := by
  rw [crossDistanceWeight, ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

theorem measurable_passingDistanceFourierIntegrand {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) (r : ℝ) : Measurable (passingDistanceFourierIntegrand Z r) := by
  have hm : Measurable (Z.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hZ
  unfold passingDistanceFourierIntegrand
  exact ((by fun_prop : Measurable (fun p : Plane × Plane ↦
      Complex.exp (-((r * dist p.1 p.2 : ℝ) : ℂ) * Complex.I) *
        Complex.ofReal ((Real.sqrt (dist p.1 p.2))⁻¹))).mul hm.complex_ofReal)

theorem norm_passingDistanceFourierIntegrand (Z : Set (Plane × Plane)) (r : ℝ)
    (p : Plane × Plane) :
    ‖passingDistanceFourierIntegrand Z r p‖ =
      (crossDistanceWeight p).toReal * Z.indicator (fun _ ↦ (1 : ℝ)) p := by
  by_cases hp : p ∈ Z <;>
    simp [passingDistanceFourierIntegrand, hp, Complex.norm_exp, toReal_crossDistanceWeight]

theorem integrable_passingDistanceFourierIntegrand (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) (r : ℝ) :
    Integrable (passingDistanceFourierIntegrand Z r) ((ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  apply (integrable_const ((Real.sqrt d)⁻¹)).mono
    (measurable_passingDistanceFourierIntegrand hZ r).aestronglyMeasurable
  filter_upwards [ae_restricted_product_carriers ρ₁ ρ₂ hX hY] with p hp
  rw [norm_passingDistanceFourierIntegrand, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg d))]
  have hw := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (crossDistanceWeight_le_of_dist hd (hsep p.1 hp.1 p.2 hp.2))
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.sqrt_nonneg d))] at hw
  by_cases hz : p ∈ Z
  · simpa only [indicator_of_mem hz, mul_one] using hw
  · simp only [indicator_of_notMem hz, mul_zero]
    positivity

/-- The actual distance transform equals the literal weighted spatial oscillatory integral. -/
theorem angularScalarFourier_passingWeightedDistanceMeasure_eq_integral
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) (r : ℝ) :
    angularScalarFourier (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) r =
      ∫ p, passingDistanceFourierIntegrand Z r p ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) := by
  have hm : Measurable (Z.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hZ
  have hden : Measurable (fun p ↦
      crossDistanceWeight p * ENNReal.ofReal (Z.indicator (fun _ ↦ (1 : ℝ)) p)) :=
    measurable_crossDistanceWeight.mul hm.ennreal_ofReal
  have hfin : ∀ᵐ p ∂(ρ₁.restrict X).prod (ρ₂.restrict Y),
      crossDistanceWeight p * ENNReal.ofReal (Z.indicator (fun _ ↦ (1 : ℝ)) p) < ∞ := by
    filter_upwards [ae_restricted_product_carriers ρ₁ ρ₂ hX hY] with p hp
    have hw := (crossDistanceWeight_le_of_dist hd (hsep p.1 hp.1 p.2 hp.2)).trans_lt
      ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top hw ENNReal.ofReal_lt_top
  rw [angularScalarFourier, charFun_apply_real, passingWeightedDistanceMeasure,
    filteredCrossDistanceMeasure, integral_map (by fun_prop) (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul hden hfin]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_mul, toReal_crossDistanceWeight]
  by_cases hp : p ∈ Z <;>
    simp [passingDistanceFourierIntegrand, hp, Complex.real_smul, Complex.ofReal_mul,
      mul_comm]

/-- Genuine Fubini supplies the iterated actual carrier integral needed by stationary phase. -/
theorem angularScalarFourier_passingWeightedDistanceMeasure_eq_iterated
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) (r : ℝ) :
    angularScalarFourier (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) r =
      ∫ x in X, ∫ y in Y, passingDistanceFourierIntegrand Z r (x, y) ∂ρ₂ ∂ρ₁ := by
  rw [angularScalarFourier_passingWeightedDistanceMeasure_eq_integral ρ₁ ρ₂ hX hY hd hsep hZ]
  exact integral_prod _ (integrable_passingDistanceFourierIntegrand ρ₁ ρ₂ hX hY hd hsep hZ r)

end FalconerThetaGauge
