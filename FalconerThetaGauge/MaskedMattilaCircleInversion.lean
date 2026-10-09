module

public import FalconerThetaGauge.MaskedMattilaCircleKernel

/-! # The actual spatial-pair circle-integral inversion of source (7.4) -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- Source (7.4) for the actual pair direction, actual distance and actual
circle dot-product integral, with the two genuine built symbols. -/
theorem builtSymbolPair_circle_mattila_inversion {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) {ρ₁ ρ₂ : Measure Plane} {width : ℝ}
    {I₁ I₂ : Finset ProfileScheduleTest} {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁) (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ₁ (tolerance θ N * N) width
      (8 * expansionCount θ N) I₁ (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ₂ (tolerance θ N * N) width
      (8 * expansionCount θ N) I₂ (2 * expansionCount θ N))
    {x y : Plane} (hxy : x ≠ y) {α r w : ℝ} (hr : 0 < r)
    (hdir : pairDirection x y ∈ closedDirectionArc α (1 / 40))
    (hw : 10 * (tolerance θ N * N) ≤ w)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ w + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ w + tolerance θ N * N)
    (hΛ : (2 : ℝ) ^ (w - 4) ≤ r * ‖x - y‖)
    (hdterminal : (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ ‖x - y‖) :
    ‖(Real.sqrt ‖x - y‖ : ℂ)⁻¹ *
        Complex.exp (-((r * ‖x - y‖ : ℝ) : ℂ) * Complex.I) *
        (b₁ x (pairDirection x y) * b₂ y (pairDirection x y) : ℝ) -
      preparedCircleInversionConstant * (Real.sqrt r : ℂ) *
        preparedInverseCircleKernelSeries (expansionCount θ N) α
          (builtSymbolPairAngularAmplitude b₁ b₂ x y) (x - y) r‖ ≤
      (2 : ℝ) ^ (-(200 * (N : ℝ))) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [preparedInverseCircleKernelSeries_eq_angular _ _
    (contDiff_builtSymbolPairAngularAmplitude hb₁ hb₂ x y)
    (periodic_builtSymbolPairAngularAmplitude b₁ b₂ x y) hz]
  have h := builtSymbolPair_pointwise_mattila_inversion hpar hL₁ hL₂ hc₁ hc₂ hL₁N hL₂N
    hb₁ hb₂ x y hr (norm_pos_iff.mpr hz)
    (by simpa only [pairDirection_eq_unitCircleOfAngle_difference] using hdir)
    (-Real.pi) hw hlength₁ hlength₂ hΛ hdterminal
  simpa only [← pairDirection_eq_unitCircleOfAngle_difference] using h

end FalconerThetaGauge
