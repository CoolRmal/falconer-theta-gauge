module

public import FalconerThetaGauge.DistanceLinearizationMassEstimate
public import FalconerThetaGauge.DistanceLinearizationMassEnergy

/-! # The genuine weighted distance-energy recurrence of source Estimate 7.7 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The true singular distance weight contributes exactly the source separation ratio `22`. -/
theorem maskedDistanceEnergy_le_of_raw_collision (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a p t : ℕ} {A B : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    {Z Z' : Set (Plane × Plane)} (hZ : MeasurableSet Z) (hZ' : MeasurableSet Z')
    {C : ℝ} (hC : 0 ≤ C)
    (hraw : (scalarCollisionMass
        (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B) Z)
        (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B) Z)
        (dyadicRadius t) 0).toReal ≤ C *
      (scalarCollisionMass
        (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B) Z')
        (passingUnweightedDistanceMeasure ρ ρ (dyadicCube a A) (dyadicCube a B) Z')
        (dyadicRadius p) 0).toReal) :
    maskedDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B) Z t ≤
      22 * C * ((2 : ℝ) ^ t / (2 : ℝ) ^ p) *
        maskedDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B) Z' p := by
  have henergy : unweightedDistanceCollisionEnergy ρ ρ
      (dyadicCube a A) (dyadicCube a B) Z t ≤
        C * ((2 : ℝ) ^ t / (2 : ℝ) ^ p) *
          unweightedDistanceCollisionEnergy ρ ρ (dyadicCube a A) (dyadicCube a B) Z' p := by
    have h := mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ (2 : ℝ) ^ t / (ρ.real (dyadicCube a A) * ρ.real (dyadicCube a B)) by
        positivity)
    unfold unweightedDistanceCollisionEnergy
    dsimp only [dyadicRadius] at h
    convert h using 1
    simp only [div_eq_mul_inv]
    field_simp [pow_ne_zero p (by norm_num : (2 : ℝ) ≠ 0)]
  have hupper := (maskedDistanceEnergy_cells_unweighted_bounds ρ ρ hsep hZ t).2
  have hlower := (maskedDistanceEnergy_cells_unweighted_bounds ρ ρ hsep hZ' p).1
  have hcoeff : 0 ≤ 22 * C * ((2 : ℝ) ^ t / (2 : ℝ) ^ p) := by positivity
  apply hupper.trans
  apply (div_le_div_of_nonneg_right henergy
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 500) (dyadicRadius_pos a).le)).trans
  convert mul_le_mul_of_nonneg_left hlower hcoeff using 1
  field_simp
  ring

/-- The literal retained-test construction yields Estimate 7.7 with its explicit constant. -/
theorem scheduledDistanceEnergy_le_linearization_constant (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hap : a ≤ p) {A B : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hpt : p < t) (ht : t ≤ N) (hdepth : a + t < 2 * p)
    {width width' : ℝ} (hwidth' : 1 ≤ width')
    (hgap : 8 * (2 : ℝ) ^ (-(tolerance θ N * N)) ≤ width - width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest}
    (hprojection : (⟨.projection, p, t⟩) ∈ I₂)
    (hJ₁ : J₁ ⊆ I₁) (hJ₂ : J₂ ⊆ I₂)
    (hordered₁ : ScheduledTestsOrdered J₁) (hordered₂ : ScheduledTestsOrdered J₂)
    (hshort₁ : ∀ test ∈ J₁, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hshort₂ : ∀ test ∈ J₂, test.anchor ≤ p ∧ a + test.length ≤ p) :
    scheduledDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B)
        (tolerance θ N * N) width I₁ I₂ t ≤
      21384 * (2 : ℝ) ^ ((N : ℝ) *
        (profileHeight (regularMeasureExcess ρ N) p p t + 6 * tolerance θ N)) *
        scheduledDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B)
          (tolerance θ N * N) width' J₁ J₂ p := by
  have hraw := passingUnweightedCollision_toReal_le_shortened ρ hρ hpar hreg hap hsep
    hpt ht hdepth hwidth' hgap hprojection hJ₁ hJ₂ hordered₁ hordered₂ hshort₁ hshort₂
  have h := maskedDistanceEnergy_le_of_raw_collision ρ hsep
    (measurableSet_scheduledPassingPairSet ρ ρ _ _ _ _)
    (measurableSet_scheduledPassingPairSet ρ ρ _ _ _ _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 972)
      (linearizationCellCoefficient_pos ρ θ N p t).le) hraw
  change scheduledDistanceEnergy ρ ρ _ _ _ width I₁ I₂ t ≤ _ at h
  convert h using 1
  unfold linearizationCellCoefficient scheduledDistanceEnergy
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

/-- The numerical hypotheses absorb the genuine `21384` into the manuscript's `7ε` exponent. -/
theorem linearization_constant_le_height (ρ : Measure Plane) {θ : ℝ} {N p t : ℕ}
    (hpar : ParameterFacts θ N) :
    21384 * (2 : ℝ) ^ ((N : ℝ) *
      (profileHeight (regularMeasureExcess ρ N) p p t + 6 * tolerance θ N)) ≤
      (2 : ℝ) ^ ((N : ℝ) *
        (profileHeight (regularMeasureExcess ρ N) p p t + 7 * tolerance θ N)) := by
  have hc : (21384 : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) := by
    calc
      (21384 : ℝ) ≤ (2 : ℝ) ^ (16 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (tolerance θ N * N) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hpar.2.2.1.1
  have heq : (N : ℝ) * (profileHeight (regularMeasureExcess ρ N) p p t +
      7 * tolerance θ N) = tolerance θ N * N +
        (N : ℝ) * (profileHeight (regularMeasureExcess ρ N) p p t + 6 * tolerance θ N) := by
    ring
  rw [heq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/-- Source Estimate 7.7 for the literal weighted passing measures and actual profile height. -/
theorem scheduledDistanceEnergy_le_linearization (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hap : a ≤ p) {A B : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hpt : p < t) (ht : t ≤ N) (hdepth : a + t < 2 * p)
    {width width' : ℝ} (hwidth' : 1 ≤ width')
    (hgap : 8 * (2 : ℝ) ^ (-(tolerance θ N * N)) ≤ width - width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest}
    (hprojection : (⟨.projection, p, t⟩) ∈ I₂)
    (hJ₁ : J₁ ⊆ I₁) (hJ₂ : J₂ ⊆ I₂)
    (hordered₁ : ScheduledTestsOrdered J₁) (hordered₂ : ScheduledTestsOrdered J₂)
    (hshort₁ : ∀ test ∈ J₁, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hshort₂ : ∀ test ∈ J₂, test.anchor ≤ p ∧ a + test.length ≤ p) :
    scheduledDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B)
        (tolerance θ N * N) width I₁ I₂ t ≤
      (2 : ℝ) ^ ((N : ℝ) *
        (profileHeight (regularMeasureExcess ρ N) p p t + 7 * tolerance θ N)) *
        scheduledDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B)
          (tolerance θ N * N) width' J₁ J₂ p := by
  apply (scheduledDistanceEnergy_le_linearization_constant ρ hρ hpar hreg hap hsep
    hpt ht hdepth hwidth' hgap hprojection hJ₁ hJ₂ hordered₁ hordered₂
    hshort₁ hshort₂).trans
  exact mul_le_mul_of_nonneg_right (linearization_constant_le_height ρ hpar)
    (maskedDistanceEnergy_nonneg ρ ρ _ _ _ p)

/-- Actual source mask levels supply the width conditions of Estimate 7.7. -/
theorem scheduledDistanceEnergy_level_le_linearization (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N a p t : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hap : a ≤ p) {A B : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hpt : p < t) (ht : t ≤ N) (hdepth : a + t < 2 * p)
    {L i : ℕ} (hL : 0 < L) (hi : i + 1 ≤ L)
    (hsize : (L : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8)
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest}
    (hprojection : (⟨.projection, p, t⟩) ∈ I₂)
    (hJ₁ : J₁ ⊆ I₁) (hJ₂ : J₂ ⊆ I₂)
    (hordered₁ : ScheduledTestsOrdered J₁) (hordered₂ : ScheduledTestsOrdered J₂)
    (hshort₁ : ∀ test ∈ J₁, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hshort₂ : ∀ test ∈ J₂, test.anchor ≤ p ∧ a + test.length ≤ p) :
    scheduledDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B)
        (tolerance θ N * N) (directionalLevelWidth L i) I₁ I₂ t ≤
      (2 : ℝ) ^ ((N : ℝ) *
        (profileHeight (regularMeasureExcess ρ N) p p t + 7 * tolerance θ N)) *
        scheduledDistanceEnergy ρ ρ (dyadicCube a A) (dyadicCube a B)
          (tolerance θ N * N) (directionalLevelWidth L (i + 1)) J₁ J₂ p :=
  scheduledDistanceEnergy_le_linearization ρ hρ hpar hreg hap hsep hpt ht hdepth
    (directionalLevelWidth_mem_Icc hL hi).1
    (directionalLevelWidth_gap_ge hL _ hsize i) hprojection hJ₁ hJ₂
    hordered₁ hordered₂ hshort₁ hshort₂

end FalconerThetaGauge
