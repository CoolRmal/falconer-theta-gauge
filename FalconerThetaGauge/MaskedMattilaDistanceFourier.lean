/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaSeriesEnergy
public import FalconerThetaGauge.MaskedMattilaCircleInversion

/-! # The actual masked distance transform used in the Mattila estimate -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric
open scoped Classical ContDiff ENNReal

namespace FalconerThetaGauge

def maskedDistancePairFourierIntegrand (b₁ b₂ : Plane → UnitCircle → ℝ)
    (r : ℝ) (p : Plane × Plane) : ℂ :=
  Complex.exp (-((r * dist p.1 p.2 : ℝ) : ℂ) * Complex.I) *
    ((Real.sqrt (dist p.1 p.2))⁻¹ : ℝ) * (directionalPairMask b₁ b₂ p : ℂ)

theorem integrable_maskedDistancePairFourierIntegrand
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (r : ℝ) :
    Integrable (maskedDistancePairFourierIntegrand b₁ b₂ r)
      ((ρ₁.restrict X).prod (ρ₂.restrict Y)) := by
  have hi := (integrable_passingDistanceFourierIntegrand ρ₁ ρ₂ hX hY hd hsep
    MeasurableSet.univ r).norm
  apply hi.mono ?_ ?_
  · exact ((by fun_prop : Measurable (fun p : Plane × Plane ↦
        Complex.exp (-((r * dist p.1 p.2 : ℝ) : ℂ) * Complex.I) *
          (((Real.sqrt (dist p.1 p.2))⁻¹ : ℝ) : ℂ))).mul
      (measurable_directionalPairMask hb₁ hb₂).complex_ofReal).aestronglyMeasurable
  · filter_upwards [] with p
    have he : ‖maskedDistancePairFourierIntegrand b₁ b₂ r p‖ =
        ‖passingDistanceFourierIntegrand univ r p‖ *
          |b₁ p.1 (pairDirection p.1 p.2)| * |b₂ p.2 (pairDirection p.1 p.2)| := by
      simp [maskedDistancePairFourierIntegrand, passingDistanceFourierIntegrand,
        directionalPairMask, Complex.norm_exp, mul_assoc]
    rw [he, Real.norm_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ‖passingDistanceFourierIntegrand univ r p‖ * 1 * 1 := by
        gcongr
        · exact hbound₁ _ _
        · exact hbound₂ _ _
      _ = _ := by ring

theorem angularScalarFourier_maskedDistance_eq_integral
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, b₁ x w ∈ Icc 0 1)
    (hbound₂ : ∀ x w, b₂ x w ∈ Icc 0 1) (r : ℝ) :
    angularScalarFourier (filteredCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y)
      (directionalPairMask b₁ b₂)) r =
      ∫ p, maskedDistancePairFourierIntegrand b₁ b₂ r p
        ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) := by
  have hm := measurable_directionalPairMask hb₁ hb₂
  have hden : Measurable (fun p ↦ crossDistanceWeight p *
      ENNReal.ofReal (directionalPairMask b₁ b₂ p)) :=
    measurable_crossDistanceWeight.mul hm.ennreal_ofReal
  have hfin : ∀ᵐ p ∂(ρ₁.restrict X).prod (ρ₂.restrict Y), crossDistanceWeight p *
      ENNReal.ofReal (directionalPairMask b₁ b₂ p) < (⊤ : ℝ≥0∞) := by
    filter_upwards [ae_restricted_product_carriers ρ₁ ρ₂ hX hY] with p hp
    exact ENNReal.mul_lt_top
      ((crossDistanceWeight_le_of_dist hd (hsep p.1 hp.1 p.2 hp.2)).trans_lt
        ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  rw [angularScalarFourier, charFun_apply_real, filteredCrossDistanceMeasure,
    integral_map (by fun_prop) (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul hden hfin]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_mul, toReal_crossDistanceWeight,
    ENNReal.toReal_ofReal (directionalPairMask_mem_Icc hbound₁ hbound₂ p).1]
  have hphase : ((-r : ℝ) : ℂ) * (dist p.1 p.2 : ℂ) * Complex.I =
      -((r * dist p.1 p.2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simp only [maskedDistancePairFourierIntegrand, Complex.real_smul, hphase,
    Complex.ofReal_mul]
  ring

theorem isFiniteMeasure_maskedDistance (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hbound₁ : ∀ x w, b₁ x w ∈ Icc 0 1)
    (hbound₂ : ∀ x w, b₂ x w ∈ Icc 0 1) :
    IsFiniteMeasure (filteredCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y)
      (directionalPairMask b₁ b₂)) := by
  have hi := isFiniteMeasure_passingWeightedDistanceMeasure ρ₁ ρ₂ hX hY univ
    (fun x hx y hy ↦ crossDistanceWeight_le_of_dist hd (hsep x hx y hy))
  have he : passingWeightedDistanceMeasure ρ₁ ρ₂ X Y univ =
      weightedCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y) := by
    simp [passingWeightedDistanceMeasure, filteredCrossDistanceMeasure,
      weightedCrossDistanceMeasure]
  rw [he] at hi
  let : IsFiniteMeasure (weightedCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y)) := hi
  exact isFiniteMeasure_filteredCrossDistanceMeasure _ _
    (Eventually.of_forall (fun p ↦ (directionalPairMask_mem_Icc hbound₁ hbound₂ p).2))

end FalconerThetaGauge
