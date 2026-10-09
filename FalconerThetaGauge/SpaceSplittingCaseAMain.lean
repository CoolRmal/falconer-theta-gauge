module

public import FalconerThetaGauge.SpaceSplittingCaseACircleBound

/-! # The actual Case A stationary main term is the sum of its genuine radial terms -/

@[expose] public section

noncomputable section

open MeasureTheory Function Finset

namespace FalconerThetaGauge

theorem orthogonalityRadialAmplitude_mul_spaceSplittingStationaryMain_eq
    (K v T : ℕ) (b : Plane → UnitCircle → ℝ) (r : ℝ) (x x' : Plane) :
    orthogonalityRadialAmplitude K v r * spaceSplittingStationaryMain T b r x x' =
      ∑ j ∈ range T,
        (spaceSplittingCaseAStationaryTerm K v j 1 (dist x x')
          (stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
            (radialAngle 0 (x - x'))) r +
        spaceSplittingCaseAStationaryTerm K v j (-1) (dist x x')
          (stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
            (radialAngle 0 (x - x') + Real.pi)) r) := by
  unfold spaceSplittingStationaryMain spaceSplittingCaseAStationaryTerm
  simp only [one_mul, neg_one_mul, Complex.ofReal_neg, neg_neg, mul_add, mul_sum]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

theorem integral_spaceSplittingStationaryMain_circle_eq_sum (K v T : ℕ)
    (b₁ : Plane → UnitCircle → ℝ) {b₂ : Plane → UnitCircle → ℝ}
    (hb₂ : Measurable (uncurry b₂)) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) (hd : 0 < dist x x') :
    (∫ r : ℝ, orthogonalityRadialAmplitude K v r *
      spaceSplittingStationaryMain T b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y') =
      ∑ j ∈ range T,
        ((∫ r : ℝ, spaceSplittingCaseAStationaryTerm K v j 1 (dist x x')
          (stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
            (radialAngle 0 (x - x'))) r * spaceSplittingCircleIntegral b₂ r y y') +
        ∫ r : ℝ, spaceSplittingCaseAStationaryTerm K v j (-1) (dist x x')
          (stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
            (radialAngle 0 (x - x') + Real.pi)) r *
              spaceSplittingCircleIntegral b₂ r y y') := by
  have hi (j : ℕ) (σ : ℝ) (c : ℂ) :=
    integrable_spaceSplittingCaseAStationaryTerm_circle K v j σ (dist x x') c hd
      hb₂ hbound₂ y y'
  calc
    _ = ∫ r : ℝ, ∑ j ∈ range T,
        (spaceSplittingCaseAStationaryTerm K v j 1 (dist x x')
          (stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
            (radialAngle 0 (x - x'))) r * spaceSplittingCircleIntegral b₂ r y y' +
        spaceSplittingCaseAStationaryTerm K v j (-1) (dist x x')
          (stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
            (radialAngle 0 (x - x') + Real.pi)) r *
              spaceSplittingCircleIntegral b₂ r y y') := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [orthogonalityRadialAmplitude_mul_spaceSplittingStationaryMain_eq,
        sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      have hs := integral_finsetSum (range T) (fun j _ ↦
        (hi j 1 (stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
          (radialAngle 0 (x - x')))).add
        (hi j (-1) (stationaryPhaseConjugateOperator j
          (builtSymbolPairAngularAmplitude b₁ b₁ x x')
          (radialAngle 0 (x - x') + Real.pi))))
      simp only [Pi.add_apply] at hs
      rw [hs]
      apply sum_congr rfl
      intro j _
      exact integral_add (hi j 1 _) (hi j (-1) _)

theorem integrable_spaceSplittingStationaryMain_circle (K v T : ℕ)
    (b₁ : Plane → UnitCircle → ℝ) {b₂ : Plane → UnitCircle → ℝ}
    (hb₂ : Measurable (uncurry b₂)) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (x x' y y' : Plane) (hd : 0 < dist x x') :
    Integrable (fun r : ℝ ↦ orthogonalityRadialAmplitude K v r *
      spaceSplittingStationaryMain T b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y') := by
  have hi (j : ℕ) (σ : ℝ) (c : ℂ) :=
    integrable_spaceSplittingCaseAStationaryTerm_circle K v j σ (dist x x') c hd
      hb₂ hbound₂ y y'
  have hsum := integrable_finsetSum (range T) (fun j _ ↦
    (hi j 1 (stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
      (radialAngle 0 (x - x')))).add
    (hi j (-1) (stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b₁ b₁ x x')
      (radialAngle 0 (x - x') + Real.pi))))
  convert hsum using 1
  funext r
  rw [orthogonalityRadialAmplitude_mul_spaceSplittingStationaryMain_eq, sum_mul]
  apply sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  ring

end FalconerThetaGauge
