module

public import FalconerThetaGauge.SpaceSplittingOppositeSeries
public import FalconerThetaGauge.SpaceSplittingSupport

/-! # Literal passing indicators in the opposite-sign space-splitting kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

namespace FalconerThetaGauge

def spaceSplittingBuiltOppositeSeries (K v T : ℕ) (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x x' y y' : Plane) : ℂ :=
  spaceSplittingOppositeRadialSeries K v T (dist x x') (dist y y')
    (builtSymbolPairAngularAmplitude b₁ b₁ x x')
    (builtSymbolPairAngularAmplitude b₂ b₂ y y')
    (radialAngle 0 (x - x')) (radialAngle 0 (y - y'))

theorem stationaryPhaseCoefficients_eq_zero_of_not_passingPair
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K k₀ : ℕ) (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    {x x' : Plane} (hxx' : x ≠ x')
    (hfail : (x, x') ∉ scheduledPassingPairSet ρ ρ E
      (directionalLevelWidth levels (i + 1)) I I) (j : ℕ) :
    stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
        (radialAngle 0 (x - x')) = 0 ∧
      stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
        (radialAngle 0 (x - x') + Real.pi) = 0 := by
  by_contra hn
  exact hfail (stationaryPhaseCoefficients_ne_zero_implies_passingPair ρ E hlevels hsize
    i K k₀ I hordered hb hxx' (not_and_or.mp hn))

theorem spaceSplittingBuiltOppositeSeries_eq_zero_of_not_passing
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K k₀ radialOrder v T : ℕ) (I : Finset ProfileScheduleTest)
    (hordered : ScheduledTestsOrdered I) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    {x x' y y' : Plane} (hxx' : x ≠ x') (hyy' : y ≠ y')
    (hfail : (x, x') ∉ scheduledPassingPairSet ρ ρ E
        (directionalLevelWidth levels (i + 1)) I I ∨
      (y, y') ∉ scheduledPassingPairSet ρ ρ E
        (directionalLevelWidth levels (i + 1)) I I) :
    spaceSplittingBuiltOppositeSeries radialOrder v T b₁ b₂ x x' y y' = 0 := by
  rcases hfail with hx | hy
  · have hz := stationaryPhaseCoefficients_eq_zero_of_not_passingPair ρ E hlevels hsize
      i K k₀ I hordered hb₁ hxx' hx
    simp only [spaceSplittingBuiltOppositeSeries, spaceSplittingOppositeRadialSeries,
      spaceSplittingOppositeTerm, (hz _).1, (hz _).2, zero_div, zero_mul, mul_zero,
      add_zero, sum_const_zero]
  · have hz := stationaryPhaseCoefficients_eq_zero_of_not_passingPair ρ E hlevels hsize
      i K k₀ I hordered hb₂ hyy' hy
    simp only [spaceSplittingBuiltOppositeSeries, spaceSplittingOppositeRadialSeries,
      spaceSplittingOppositeTerm, (hz _).1, (hz _).2, zero_div, zero_mul, mul_zero,
      add_zero, sum_const_zero]

/-- Equation (7.6), including the actual next-level passing conditions at all four points. -/
theorem norm_spaceSplittingBuiltOppositeSeries_le_passing_kernel
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i : ℕ) {radialOrder v T : ℕ} (hK : 2 ≤ radialOrder)
    (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I) {L : ℕ}
    (hL : ∀ test ∈ I, test.length ≤ L) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) (8 * T) I (2 * T))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) (8 * T) I (2 * T))
    {x x' y y' : Plane} (hdx : 0 < dist x x') (hdy : 0 < dist y y')
    (hxscale : 1600 * T * (max 1 (scheduledSymbolScale T E I L)) ^ 2 /
      ((2 : ℝ) ^ v * dist x x') ≤ 1 / 4)
    (hyscale : 1600 * T * (max 1 (scheduledSymbolScale T E I L)) ^ 2 /
      ((2 : ℝ) ^ v * dist y y') ≤ 1 / 4) :
    ‖spaceSplittingBuiltOppositeSeries radialOrder v T b₁ b₂ x x' y y'‖ ≤
      ((2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v / Real.sqrt (dist x x' * dist y y') /
        (1 + (2 : ℝ) ^ v * |dist x x' - dist y y'|) ^ 2) *
      (scheduledPassingPairSet ρ ρ E (directionalLevelWidth levels (i + 1)) I I).indicator
        (fun _ ↦ (1 : ℝ)) (x, x') *
      (scheduledPassingPairSet ρ ρ E (directionalLevelWidth levels (i + 1)) I I).indicator
        (fun _ ↦ (1 : ℝ)) (y, y') := by
  classical
  let Z := scheduledPassingPairSet ρ ρ E (directionalLevelWidth levels (i + 1)) I I
  by_cases hx : (x, x') ∈ Z
  · by_cases hy : (y, y') ∈ Z
    · simp only [show (x, x') ∈ scheduledPassingPairSet ρ ρ E
        (directionalLevelWidth levels (i + 1)) I I from hx,
        show (y, y') ∈ scheduledPassingPairSet ρ ρ E
          (directionalLevelWidth levels (i + 1)) I I from hy,
        indicator_of_mem, mul_one]
      have hxreg := builtSymbolPairAngularAmplitude_isDerivativeRegular hL hL hb₁ hb₁ x x'
      have hyreg := builtSymbolPairAngularAmplitude_isDerivativeRegular hL hL hb₂ hb₂ y y'
      rw [← two_mul] at hxreg hyreg
      exact norm_spaceSplittingOppositeRadialSeries_le hK hdx hdy hxreg hyreg
        hxscale hyscale _ _
    · rw [spaceSplittingBuiltOppositeSeries_eq_zero_of_not_passing ρ E hlevels hsize
        i (8 * T) (2 * T) radialOrder v T I hordered hb₁ hb₂
        (dist_pos.1 hdx) (dist_pos.1 hdy) (Or.inr hy)]
      have hy' : (y, y') ∉ scheduledPassingPairSet ρ ρ E
        (directionalLevelWidth levels (i + 1)) I I := hy
      simp only [norm_zero, indicator_of_notMem hy', mul_zero, le_refl]
  · rw [spaceSplittingBuiltOppositeSeries_eq_zero_of_not_passing ρ E hlevels hsize
      i (8 * T) (2 * T) radialOrder v T I hordered hb₁ hb₂
      (dist_pos.1 hdx) (dist_pos.1 hdy) (Or.inl hx)]
    have hx' : (x, x') ∉ scheduledPassingPairSet ρ ρ E
      (directionalLevelWidth levels (i + 1)) I I := hx
    simp only [norm_zero, indicator_of_notMem hx', mul_zero, zero_mul, le_refl]

end FalconerThetaGauge
