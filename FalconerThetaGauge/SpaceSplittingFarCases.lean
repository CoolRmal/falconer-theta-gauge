module

public import FalconerThetaGauge.SpaceSplittingFarCaseA
public import FalconerThetaGauge.SpaceSplittingFarKernelFinite
public import FalconerThetaGauge.SpaceSplittingCaseB

/-! # The true far-cell kernel bound includes all actual analytic cases -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem ofReal_norm_spaceSplittingAveragedCircleKernel_far_le
    (ρ : Measure Plane) [IsFiniteMeasure ρ] {θ : ℝ} {N L p v levels : ℕ}
    (hpar : ParameterFacts θ N) (hlevels : 0 < levels)
    (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8) (i : ℕ)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hordered : ScheduledTestsOrdered I) (hL : L ≤ N)
    (hlength : ∀ test ∈ I, test.length ≤ L) (hp : p ≤ N) (hv : v ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - p)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} (hfar : ¬spaceSplittingNear p R S)
    {x x' y y' : Plane} (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2) :
    ENNReal.ofReal ‖spaceSplittingAveragedCircleKernel b₁ b₂
      (8 * expansionCount θ N) v x x' y y'‖ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (25 : ℕ)) * ENNReal.ofReal ((2 : ℝ) ^ v) *
        spaceSplittingFarWeightedKernel p v
          (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
            (directionalLevelWidth levels (i + 1)) I I)
          (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
            (directionalLevelWidth levels (i + 1)) I I) ((x, x'), (y, y')) +
      ENNReal.ofReal ((2 : ℝ) ^ (-300 * (N : ℝ))) := by
  classical
  let Z := scheduledPassingPairSet ρ ρ (tolerance θ N * N)
    (directionalLevelWidth levels (i + 1)) I I
  have hp' : (p : ℝ) ≤ N := by exact_mod_cast hp
  by_cases hc : max (dist x x') (dist y y') ≤ 2 * min (dist x x') (dist y y')
  · have hq := (spaceSplittingFar_mem_comparable_iff hfar hx hx' hy hy').2 hc
    have hds := spaceSplittingFar_comparable_distance_gt hfar hx hx' hy hy' hc
    have hdx : (5 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℝ)) ≤ dist x x' :=
      by simpa only [dyadicRadius] using hds.1.le
    have hdy : (5 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℝ)) ≤ dist y y' :=
      by simpa only [dyadicRadius] using hds.2.le
    have hx₀ : 0 < dist x x' := lt_of_lt_of_le (by positivity) hdx
    have hy₀ : 0 < dist y y' := lt_of_lt_of_le (by positivity) hdy
    have hB := norm_spaceSplittingAveragedCircleKernel_caseB_le_source ρ hpar hlevels hsize
      i I hcard hordered hL hv hp' hgap hlength hb₁ hb₂ hdx hdy
    have hδ : (2 : ℝ) ^ (-380 * (N : ℝ)) ≤ (2 : ℝ) ^ (-300 * (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    let C : ℝ := ((2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v /
      Real.sqrt (dist x x' * dist y y') /
        (1 + (2 : ℝ) ^ v * |dist x x' - dist y y'|) ^ 2) *
          Z.indicator (fun _ ↦ (1 : ℝ)) (x, x') *
          Z.indicator (fun _ ↦ (1 : ℝ)) (y, y')
    have hZx : 0 ≤ Z.indicator (fun _ ↦ (1 : ℝ)) (x, x') :=
      indicator_nonneg (fun _ _ ↦ by norm_num) _
    have hZy : 0 ≤ Z.indicator (fun _ ↦ (1 : ℝ)) (y, y') :=
      indicator_nonneg (fun _ _ ↦ by norm_num) _
    have hC : 0 ≤ C := by dsimp [C]; exact mul_nonneg (mul_nonneg (by positivity) hZx) hZy
    change ‖spaceSplittingAveragedCircleKernel b₁ b₂ (8 * expansionCount θ N) v
      x x' y y'‖ ≤ C + (2 : ℝ) ^ (-380 * (N : ℝ)) at hB
    have he := ENNReal.ofReal_le_ofReal (hB.trans (add_le_add (le_refl C) hδ))
    rw [ENNReal.ofReal_add hC (by positivity),
      ofReal_spaceSplitting_passing_coefficient_eq_weighted hx₀ hy₀ Z Z v] at he
    simpa only [spaceSplittingFarWeightedKernel, indicator_of_mem hq] using he
  · have hq : ((x, x'), (y, y')) ∉ spaceSplittingFarComparableSet p := fun hh ↦ hc hh.2
    simp only [spaceSplittingFarWeightedKernel, indicator_of_notMem hq, mul_zero, zero_add]
    exact ENNReal.ofReal_le_ofReal
      (norm_spaceSplittingAveragedCircleKernel_far_noncomparable_le_source hpar I hcard hL
        hlength hp hv hgap hb₁ hb₂ hfar hx hx' hy hy' hc)

theorem norm_spaceSplittingAveragedCircleKernel_far_le_source
    (ρ : Measure Plane) [IsFiniteMeasure ρ] {θ : ℝ} {N L p v levels : ℕ}
    (hpar : ParameterFacts θ N) (hlevels : 0 < levels)
    (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8) (i : ℕ)
    (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hordered : ScheduledTestsOrdered I) (hL : L ≤ N)
    (hlength : ∀ test ∈ I, test.length ≤ L) (hp : p ≤ N) (hv : v ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - p)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels i) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} (hfar : ¬spaceSplittingNear p R S)
    {x x' y y' : Plane} (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2) :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ (8 * expansionCount θ N) v x x' y y'‖ ≤
      (2 : ℝ) ^ (-300 * (N : ℝ)) + ((2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v) *
        (spaceSplittingFarComparableSet p).indicator
          (fun z ↦ (spaceSplittingWeightedKernel ((2 : ℝ) ^ (-(v : ℝ)))
            (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
              (directionalLevelWidth levels (i + 1)) I I)
            (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
              (directionalLevelWidth levels (i + 1)) I I) z).toReal)
          ((x, x'), (y, y')) := by
  have he := ofReal_norm_spaceSplittingAveragedCircleKernel_far_le ρ hpar hlevels hsize i I
    hcard hordered hL hlength hp hv hgap hb₁ hb₂ hfar hx hx' hy hy'
  let W := spaceSplittingFarWeightedKernel p v
    (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
      (directionalLevelWidth levels (i + 1)) I I)
    (scheduledPassingPairSet ρ ρ (tolerance θ N * N)
      (directionalLevelWidth levels (i + 1)) I I) ((x, x'), (y, y'))
  have hfinite : W ≠ ∞ := spaceSplittingFarWeightedKernel_ne_top p v _ _ _
  have hprod : ENNReal.ofReal ((2 : ℝ) ^ (25 : ℕ)) * ENNReal.ofReal ((2 : ℝ) ^ v) * W ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hfinite
  have hrhs : ENNReal.ofReal ((2 : ℝ) ^ (25 : ℕ)) * ENNReal.ofReal ((2 : ℝ) ^ v) * W +
      ENNReal.ofReal ((2 : ℝ) ^ (-300 * (N : ℝ))) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hprod, ENNReal.ofReal_ne_top⟩
  have hh := ENNReal.toReal_mono hrhs he
  rw [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_add
    hprod ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hh
  dsimp only [W] at hh
  rw [spaceSplittingFarWeightedKernel_toReal] at hh
  exact hh.trans_eq (add_comm _ _)

end FalconerThetaGauge
