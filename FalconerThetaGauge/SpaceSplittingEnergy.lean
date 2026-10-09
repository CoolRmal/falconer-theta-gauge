module

public import FalconerThetaGauge.SpaceSplittingEnergyNormalization
public import FalconerThetaGauge.SpaceSplittingFarSumENNWeighted
public import FalconerThetaGauge.SpaceSplittingFarCases

/-! # The complete actual space-splitting estimate, source Estimate 7.8 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped ENNReal Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- All genuine analytic cases and true finite spatial regrouping give the far term. -/
theorem spaceSplittingFarCrossSum_le_source (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N L a p v levels : ℕ}
    (hpar : ParameterFacts θ N) (hlevels : 0 < levels)
    (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8) (i : ℕ)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hordered : ScheduledTestsOrdered I) (hL : L ≤ N)
    (hlength : ∀ test ∈ I, test.length ≤ L) (hap : a ≤ p) (hp : p ≤ N) (hv : v ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N)) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ (8 * expansionCount θ N) v ≤
      (2 : ℝ) ^ (-300 * (N : ℝ)) *
        (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
      (2 : ℝ) ^ (90 : ℕ) * ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) *
        ∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDistanceMaximum ρ a n X Y
          (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
            (directionalLevelWidth levels (i + 1)) I I) v := by
  have hm₁ := measurable_of_mem_scheduledSymbolClass ρ _ _ _ _ _ hb₁
  have hm₂ := measurable_of_mem_scheduledSymbolClass ρ _ _ _ _ _ hb₂
  have hbound₁ := abs_le_one_of_mem_scheduledSymbolClass ρ _ _ _ _ (by omega) hb₁
  have hbound₂ := abs_le_one_of_mem_scheduledSymbolClass ρ _ _ _ _ (by omega) hb₂
  apply spaceSplittingFarCrossSum_le_distance_maxima_of_ofReal_bound ρ hρ hap X Y
    hm₁ hm₂ hbound₁ hbound₂ (8 * expansionCount θ N) v (by positivity)
    (measurableSet_scheduledPassingPairSet ρ ρ _ _ _ _)
  intro P _ Q _ hfar x hx x' hx' y hy y' hy'
  exact ofReal_norm_spaceSplittingAveragedCircleKernel_far_le ρ hpar hlevels hsize i I
    hcard hordered hL hlength hp hv hgap hb₁ hb₂ hfar hx hx' hy hy'

/-- Estimate 7.8 for the actual Fourier energies, including the genuine zero-mass case. -/
theorem maskedFourierEnergy_spaceSplitting_le_source
    (ρ : Measure Plane) [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1)
    {θ : ℝ} {N L a p v levels : ℕ} (hpar : ParameterFacts θ N) (hlevels : 0 < levels)
    (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8) (i : ℕ)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hordered : ScheduledTestsOrdered I) (hL : L ≤ N)
    (hlength : ∀ test ∈ I, test.length ≤ L) (hap : a ≤ p) (hp : p ≤ N) (hv : v ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N)) :
    maskedFourierEnergy ρ ρ (dyadicCube a X) (dyadicCube a Y) b₁ b₂
        (8 * expansionCount θ N) v ≤
      (81 : ℝ) ^ 2 * spaceSplittingFineEnergyAverage ρ a p X Y b₁ b₂
        (8 * expansionCount θ N) v +
      (2 : ℝ) ^ (90 : ℕ) *
        (∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDistanceMaximum ρ a n X Y
          (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
            (directionalLevelWidth levels (i + 1)) I I) v) +
      (2 : ℝ) ^ (-25 * (N : ℝ)) := by
  let m := ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)
  let Z := scheduledPassingPairSet ρ ρ (tolerance θ N * N)
    (directionalLevelWidth levels (i + 1)) I I
  let D := ∑ n ∈ Finset.Ioo a (p + 12), spaceSplittingDistanceMaximum ρ a n X Y Z v
  let δ := (2 : ℝ) ^ (-300 * (N : ℝ))
  have hm₀ : 0 ≤ m := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hm₁ : m ≤ 1 := by
    exact (mul_le_mul (measureReal_le_one (μ := ρ)) (measureReal_le_one (μ := ρ))
      measureReal_nonneg (by norm_num)).trans_eq (one_mul 1)
  have hmB₁ := measurable_of_mem_scheduledSymbolClass ρ _ _ _ _ _ hb₁
  have hmB₂ := measurable_of_mem_scheduledSymbolClass ρ _ _ _ _ _ hb₂
  have hbound₁ := abs_le_one_of_mem_scheduledSymbolClass ρ _ _ _ _ (by omega) hb₁
  have hbound₂ := abs_le_one_of_mem_scheduledSymbolClass ρ _ _ _ _ (by omega) hb₂
  have hδ : 0 ≤ δ := by positivity
  have hD : 0 ≤ D := by
    apply sum_nonneg
    intro n _
    unfold spaceSplittingDistanceMaximum
    exact finiteEnergyMaximum_nonneg _ _
  have herr : δ ≤ (2 : ℝ) ^ (-25 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  by_cases hm : 0 < m
  · have hfar := spaceSplittingFarCrossSum_le_source ρ hρ hpar hlevels hsize i I hcard
      hordered hL hlength hap hp hv hgap X Y hb₁ hb₂
    have hfar' : spaceSplittingFarCrossSum ρ a p X Y b₁ b₂
        (8 * expansionCount θ N) v ≤ δ * m ^ 2 + (2 : ℝ) ^ (90 : ℕ) * m * D := by
      convert hfar using 1
      dsimp only [m, D, δ, Z]
      ring
    have hdiv : spaceSplittingFarCrossSum ρ a p X Y b₁ b₂
        (8 * expansionCount θ N) v / m ≤ (2 : ℝ) ^ (90 : ℕ) * D + δ * m := by
      apply (div_le_iff₀ hm).2
      convert hfar' using 1
      ring
    have hnear := maskedFourierEnergy_le_normalized_near_and_far ρ hρ hap X Y
      hmB₁ hmB₂ hbound₁ hbound₂ (8 * expansionCount θ N) v hm
    apply hnear.trans
    have hδm := mul_le_mul_of_nonneg_left hm₁ hδ
    change _ ≤ (81 : ℝ) ^ 2 * _ + (2 : ℝ) ^ (90 : ℕ) * D + _
    linarith
  · have hmzero : m = 0 := le_antisymm (le_of_not_gt hm) hm₀
    have hz := maskedFourierEnergy_le ρ ρ (dyadicCube a X) (dyadicCube a Y)
      hmB₁ hmB₂ hbound₁ hbound₂ (8 * expansionCount θ N) v
    change _ ≤ 2600 * (4 : ℝ) ^ v * m at hz
    rw [hmzero, mul_zero] at hz
    apply hz.trans
    change 0 ≤ (81 : ℝ) ^ 2 * _ + (2 : ℝ) ^ (90 : ℕ) * D + _
    have hnear := spaceSplittingFineEnergyAverage_nonneg ρ a p X Y b₁ b₂
      (8 * expansionCount θ N) v
    positivity

end FalconerThetaGauge
