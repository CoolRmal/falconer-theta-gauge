module

public import FalconerThetaGauge.SpaceSplittingFarCasesGeometry
public import FalconerThetaGauge.SpaceSplittingCaseASymmetric

/-! # Every actual far fine-cell term outside the comparable set has source decay -/

@[expose] public section

noncomputable section

open MeasureTheory Function

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem norm_spaceSplittingAveragedCircleKernel_far_noncomparable_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L p v : ℕ} (hpar : ParameterFacts θ N)
    {width : ℝ} (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hL : L ≤ N) (hlength : ∀ test ∈ I, test.length ≤ L) (hp : p ≤ N) (hv : v ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - p)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)} (hfar : ¬spaceSplittingNear p R S)
    {x x' y y' : Plane} (hx : x ∈ dyadicCube p R.1) (hx' : x' ∈ dyadicCube p S.1)
    (hy : y ∈ dyadicCube p R.2) (hy' : y' ∈ dyadicCube p S.2)
    (hcase : ¬max (dist x x') (dist y y') ≤ 2 * min (dist x x') (dist y y')) :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ (8 * expansionCount θ N) v x x' y y'‖ ≤
      (2 : ℝ) ^ (-300 * (N : ℝ)) := by
  have hp' : (p : ℝ) ≤ N := by exact_mod_cast hp
  have hbound₁ := abs_le_one_of_mem_scheduledSymbolClass ρ _ _ _ _ (by omega) hb₁
  have hbound₂ := abs_le_one_of_mem_scheduledSymbolClass ρ _ _ _ _ (by omega) hb₂
  rcases spaceSplittingFar_not_comparable_cases hfar hx hx' hy hy' hcase with hh | hh
  · exact norm_spaceSplittingAveragedCircleKernel_caseA_le_source hpar I hcard hL hlength hv
      hp' hgap hb₁ (measurable_of_mem_scheduledSymbolClass ρ _ _ _ _ _ hb₂) hbound₂ x x' y y'
      (by simpa only [dyadicRadius] using hh.1) hh.2
  · exact norm_spaceSplittingAveragedCircleKernel_caseA_reverse_le_source hpar I hcard hL
      hlength hv hp' hgap hb₂ (measurable_of_mem_scheduledSymbolClass ρ _ _ _ _ _ hb₁)
      hbound₁ x x' y y'
      (by simpa only [dyadicRadius] using hh.1) hh.2

end FalconerThetaGauge
