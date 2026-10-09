module

public import FalconerThetaGauge.SpaceSplittingBudgetRemainder
public import FalconerThetaGauge.SpaceSplittingCircle

/-! # The actual far circular integral has a uniformly small stationary remainder -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

/-- Both genuine stationary contributions to the actual built-symbol circular integral. -/
def spaceSplittingStationaryMain (T : ℕ) (b : Plane → UnitCircle → ℝ)
    (r : ℝ) (x x' : Plane) : ℂ :=
  (Real.sqrt (2 * Real.pi / (r * dist x x')) : ℂ) *
    (Complex.exp (-((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
      ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
        stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
          (radialAngle 0 (x - x')) +
    Complex.exp (((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
      ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
        stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
          (radialAngle 0 (x - x') + Real.pi))

theorem norm_spaceSplittingCircleIntegral_sub_stationary_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L : ℕ} (hpar : ParameterFacts θ N)
    {width : ℝ} (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hL : L ≤ N) (hlength : ∀ test ∈ I, test.length ≤ L)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {h v r : ℝ} {x x' : Plane}
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ v - h)
    (hr : (2 : ℝ) ^ v / 4 ≤ r)
    (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist x x') :
    ‖spaceSplittingCircleIntegral b r x x' -
      spaceSplittingStationaryMain (expansionCount θ N) b r x x'‖ ≤
        (2 : ℝ) ^ (-400 * (N : ℝ)) := by
  have hT : 1 ≤ expansionCount θ N := Nat.ceil_pos.mpr
    (by have := tolerance_pos θ (N := N) (by have := hpar.1; omega); positivity)
  have hphase := spaceSplitting_phase_scale_ge_one hpar.2.2.1.1
    ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
      hgap) hr hd
  exact (spaceSplittingCircleIntegral_stationary hT hlength hb hphase).trans
    (spaceSplitting_stationary_remainder_le hpar I hcard hL hgap hr hd)

end FalconerThetaGauge
