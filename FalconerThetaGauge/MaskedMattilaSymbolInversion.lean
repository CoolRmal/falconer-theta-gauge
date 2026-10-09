module

public import FalconerThetaGauge.MaskedMattilaSymbolScale

/-! # Source (7.4) for the actual pair of scheduled built symbols -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

/-- The inversion is applied to the literal product of the two built symbols.
Only their actual finite test lengths, cardinalities and geometric scales enter. -/
theorem builtSymbolPair_pointwise_mattila_inversion {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) {ρ₁ ρ₂ : Measure Plane} {width : ℝ}
    {I₁ I₂ : Finset ProfileScheduleTest} {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁) (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ₁ (tolerance θ N * N) width
      (8 * expansionCount θ N) I₁ (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ₂ (tolerance θ N * N) width
      (8 * expansionCount θ N) I₂ (2 * expansionCount θ N))
    (x y : Plane) {α φ r d w : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) (u : ℝ)
    (hw : 10 * (tolerance θ N * N) ≤ w)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ w + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ w + tolerance θ N * N)
    (hΛ : (2 : ℝ) ^ (w - 4) ≤ r * d)
    (hdterminal : (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ d) :
    ‖(Real.sqrt d : ℂ)⁻¹ * Complex.exp (-((r * d : ℝ) : ℂ) * Complex.I) *
        (b₁ x (unitCircleOfAngle φ) * b₂ y (unitCircleOfAngle φ) : ℝ) -
      preparedCircleInversionConstant * (Real.sqrt r : ℂ) *
        preparedInverseCircleSeries (expansionCount θ N) α
          (builtSymbolPairAngularAmplitude b₁ b₂ x y) φ (r * d) u‖ ≤
      (2 : ℝ) ^ (-(200 * (N : ℝ))) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hT : 1 ≤ expansionCount θ N :=
    Nat.ceil_pos.mpr (by have := tolerance_pos θ hN; positivity)
  have hE₀ : 0 ≤ tolerance θ N * N := by positivity [tolerance_pos θ hN]
  have hEN : tolerance θ N * N ≤ (N : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (parameterFacts_tolerance_le_one hpar) (Nat.cast_nonneg N)
  have h := preparedInverseCircleSeries_source_error hpar
    (builtSymbolPairAngularAmplitude_isDerivativeRegular hL₁ hL₂ hb₁ hb₂ x y)
    (contDiff_builtSymbolPairAngularAmplitude hb₁ hb₂ x y)
    (periodic_builtSymbolPairAngularAmplitude b₁ b₂ x y) hr hd hφ u hw hΛ
    (builtPairSymbolScale_le_frequency hT N hE₀ hw I₁ I₂ hc₁ hc₂ hlength₁ hlength₂)
    (builtPairSymbolScale_le_terminal hT hEN I₁ I₂ hc₁ hc₂ hL₁N hL₂N) hdterminal
  simpa only [builtSymbolPairAngularAmplitude, builtSymbolAngularAmplitude, Pi.mul_apply,
    Complex.ofReal_mul] using h

end FalconerThetaGauge
