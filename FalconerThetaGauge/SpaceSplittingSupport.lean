module

public import FalconerThetaGauge.SpaceSplittingCircle
public import FalconerThetaGauge.ScheduledSymbolSupport

/-! # True stationary coefficients vanish away from next-level passing directions -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

/-- Every literal derivative branch retains the source next-level passing condition. -/
theorem iteratedDeriv_builtSymbolAngularAmplitude_eq_zero_of_not_passing
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K k₀ : ℕ) (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    {x : Plane} {θ : ℝ} {test : ProfileScheduleTest} (htest : test ∈ I)
    (hfail : (x, unitCircleOfAngle θ) ∉ scheduledPassingPinSet ρ E
      (directionalLevelWidth levels (i + 1)) test) (j : ℕ) :
    iteratedDeriv j (builtSymbolAngularAmplitude b x) θ = 0 := by
  obtain ⟨d, _, rfl⟩ := hb
  have hf := d.contDiff_symbol_comp_angle ρ E (directionalLevelWidth levels i) K I x
  unfold builtSymbolAngularAmplitude
  rw [iteratedDeriv_ofReal_eq ((hf.of_le (by simp)).contDiffAt), d.iteratedDeriv_symbol_eq]
  suffices (∑ branch : ScheduledSymbolBranch I j, d.branchCoefficient E I j branch *
      (d.branchData I j branch).symbol ρ E (directionalLevelWidth levels i) K I x
        (unitCircleOfAngle θ)) = 0 by rw [this]; simp
  apply sum_eq_zero
  intro branch _
  have hz : (d.branchData I j branch).symbol ρ E (directionalLevelWidth levels i) K I x
      (unitCircleOfAngle θ) = 0 := by
    by_contra hn
    have hclass : (d.branchData I j branch).symbol ρ E (directionalLevelWidth levels i) K I ∈
        scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I
          ((d.branchData I j branch).order I) := ⟨_, le_rfl, rfl⟩
    exact hfail (ne_zero_implies_next_passing_of_mem_scheduledSymbolClass ρ E hlevels
      hsize i K _ I hordered hclass hn test htest)
  rw [hz, mul_zero]

/-- At any failed pin, the literal pair amplitude and all of its derivatives vanish. -/
theorem iteratedDeriv_builtSymbolPairAngularAmplitude_eq_zero_of_not_passing
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K k₀ : ℕ) (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    {x x' : Plane} {θ : ℝ} {test : ProfileScheduleTest} (htest : test ∈ I)
    (hfail : (x, unitCircleOfAngle θ) ∉ scheduledPassingPinSet ρ E
      (directionalLevelWidth levels (i + 1)) test ∨
      (x', unitCircleOfAngle θ) ∉ scheduledPassingPinSet ρ E
        (directionalLevelWidth levels (i + 1)) test) (j : ℕ) :
    iteratedDeriv j (builtSymbolPairAngularAmplitude b b x x') θ = 0 := by
  have hj := ENat.natCast_le_of_coe_top_le_withTop (le_refl ∞) j
  rw [builtSymbolPairAngularAmplitude, iteratedDeriv_mul
    ((contDiff_builtSymbolAngularAmplitude hb x).of_le hj).contDiffAt
    ((contDiff_builtSymbolAngularAmplitude hb x').of_le hj).contDiffAt]
  apply sum_eq_zero
  intro k _
  rcases hfail with hfail | hfail
  · rw [iteratedDeriv_builtSymbolAngularAmplitude_eq_zero_of_not_passing ρ E hlevels hsize
      i K k₀ I hordered hb htest hfail k]
    simp
  · rw [iteratedDeriv_builtSymbolAngularAmplitude_eq_zero_of_not_passing ρ E hlevels hsize
      i K k₀ I hordered hb htest hfail (j - k)]
    simp

theorem stationaryPhaseOperators_pair_eq_zero_of_not_passing
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K k₀ : ℕ) (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    {x x' : Plane} {θ : ℝ} {test : ProfileScheduleTest} (htest : test ∈ I)
    (hfail : (x, unitCircleOfAngle θ) ∉ scheduledPassingPinSet ρ E
      (directionalLevelWidth levels (i + 1)) test ∨
      (x', unitCircleOfAngle θ) ∉ scheduledPassingPinSet ρ E
        (directionalLevelWidth levels (i + 1)) test) (j : ℕ) :
    stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x') θ = 0 ∧
      stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x') θ = 0 := by
  have hz := iteratedDeriv_builtSymbolPairAngularAmplitude_eq_zero_of_not_passing ρ E
    hlevels hsize i K k₀ I hordered hb htest hfail
  constructor
  · simp only [stationaryPhaseOperator, hz, mul_zero, sum_const_zero]
  · simp only [stationaryPhaseConjugateOperator, hz, mul_zero, sum_const_zero]

/-- Both signs of the genuine stationary operator retain the source passing condition. -/
theorem stationaryPhaseOperators_pair_ne_zero_implies_passing
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K k₀ : ℕ) (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    {x x' : Plane} {θ : ℝ} {j : ℕ}
    (hne : stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x') θ ≠ 0 ∨
      stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x') θ ≠ 0) :
    ∀ test ∈ I, (x, unitCircleOfAngle θ) ∈ scheduledPassingPinSet ρ E
        (directionalLevelWidth levels (i + 1)) test ∧
      (x', unitCircleOfAngle θ) ∈ scheduledPassingPinSet ρ E
        (directionalLevelWidth levels (i + 1)) test := by
  intro test htest
  by_contra hfail
  have hf := not_and_or.mp hfail
  have hz := stationaryPhaseOperators_pair_eq_zero_of_not_passing ρ E hlevels hsize
    i K k₀ I hordered hb htest hf j
  exact hne.elim (fun h ↦ h hz.1) (fun h ↦ h hz.2)

theorem scheduledPassingPinSet_antipodal (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (x : Plane) (w : UnitCircle) :
    (x, circleAntipode w) ∈ scheduledPassingPinSet ρ E width test ↔
      (x, w) ∈ scheduledPassingPinSet ρ E width test := by
  simp only [mem_scheduledPassingPinSet_iff, scheduledPassingDirections_antipodal]

theorem unitCircleOfAngle_radialAngle_difference {x x' : Plane} (hxx' : x ≠ x') :
    unitCircleOfAngle (radialAngle 0 (x - x')) = pairDirection x x' := by
  apply Subtype.ext
  rw [coe_unitCircleOfAngle, angularDirection_radialAngle (Ne.symm (sub_ne_zero.mpr hxx')),
    coe_pairDirection_of_ne hxx', sub_zero]

/-- The actual positive and negative coefficients vanish unless the literal point pair passes. -/
theorem stationaryPhaseCoefficients_ne_zero_implies_passingPair
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {levels : ℕ}
    (hlevels : 0 < levels) (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (i K k₀ : ℕ) (I : Finset ProfileScheduleTest) (hordered : ScheduledTestsOrdered I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K I k₀)
    {x x' : Plane} (hxx' : x ≠ x') {j : ℕ}
    (hne : stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
        (radialAngle 0 (x - x')) ≠ 0 ∨
      stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
        (radialAngle 0 (x - x') + Real.pi) ≠ 0) :
    (x, x') ∈ scheduledPassingPairSet ρ ρ E
      (directionalLevelWidth levels (i + 1)) I I := by
  have hpass : ∀ test ∈ I, (x, pairDirection x x') ∈ scheduledPassingPinSet ρ E
      (directionalLevelWidth levels (i + 1)) test ∧
      (x', pairDirection x x') ∈ scheduledPassingPinSet ρ E
        (directionalLevelWidth levels (i + 1)) test := by
    rcases hne with hne | hne
    · simpa only [unitCircleOfAngle_radialAngle_difference hxx'] using
        stationaryPhaseOperators_pair_ne_zero_implies_passing ρ E hlevels hsize i K k₀ I
          hordered hb (Or.inl hne)
    · simpa only [unitCircleOfAngle_add_pi, scheduledPassingPinSet_antipodal,
        unitCircleOfAngle_radialAngle_difference hxx'] using
        stationaryPhaseOperators_pair_ne_zero_implies_passing ρ E hlevels hsize i K k₀ I
          hordered hb (Or.inr hne)
  exact (mem_scheduledPassingPairSet_iff _ _ _ _ _ _ _).2
    ⟨fun test ht ↦ (hpass test ht).1, fun test ht ↦ (hpass test ht).2⟩

end FalconerThetaGauge
