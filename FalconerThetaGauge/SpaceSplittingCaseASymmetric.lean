module

public import FalconerThetaGauge.SpaceSplittingCaseA

/-! # The second orientation of the literal separated-scale case -/

@[expose] public section

noncomputable section

open MeasureTheory Function

namespace FalconerThetaGauge

theorem spaceSplittingAveragedCircleKernel_swap (b₁ b₂ : Plane → UnitCircle → ℝ)
    (K v : ℕ) (x x' y y' : Plane) :
    spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' =
      spaceSplittingAveragedCircleKernel b₂ b₁ K v y y' x x' := by
  rw [spaceSplittingAveragedCircleKernel_eq_full_line,
    spaceSplittingAveragedCircleKernel_eq_full_line]
  apply integral_congr_ae
  filter_upwards [] with r
  ring

theorem norm_spaceSplittingAveragedCircleKernel_caseA_reverse_le_source
    {ρ : Measure Plane} {θ : ℝ} {N L v : ℕ} (hpar : ParameterFacts θ N)
    {width : ℝ} (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (hL : L ≤ N) (hlength : ∀ test ∈ I, test.length ≤ L) (hv : v ≤ N)
    {h : ℝ} (hh : h ≤ N)
    (hgap : 2 * max (L : ℝ) (tolerance θ N * N) ≤ (v : ℝ) - h)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₁ : Measurable (uncurry b₁)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (x x' y y' : Plane) (hd : (5 / 4 : ℝ) * (2 : ℝ) ^ (-h) ≤ dist y y')
    (hfar : 2 * dist x x' < dist y y') :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ (8 * expansionCount θ N) v x x' y y'‖ ≤
      (2 : ℝ) ^ (-300 * (N : ℝ)) := by
  rw [spaceSplittingAveragedCircleKernel_swap]
  exact norm_spaceSplittingAveragedCircleKernel_caseA_le_source hpar I hcard hL hlength hv hh
    hgap hb₂ hb₁ hbound₁ y y' x x' hd hfar

end FalconerThetaGauge
