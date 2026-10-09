module

public import FalconerThetaGauge.SpaceSplittingStationaryMainProduct

/-! # Pointwise finite expansion of the literal stationary-main product -/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace FalconerThetaGauge

def spaceSplittingStationaryProductTerms (K v T : ℕ) (dx dy : ℝ)
    (Gx Gy : ℝ → ℂ) (φx φy r : ℝ) : ℂ :=
  ∑ j ∈ range T, ∑ k ∈ range T,
    (spaceSplittingStationaryRadialTerm K v j k dx dy
      (stationaryPhaseOperator j Gx φx)
      (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) (dx - dy) r +
     spaceSplittingStationaryRadialTerm K v k j dy dx
      (stationaryPhaseOperator k Gy φy)
      (stationaryPhaseConjugateOperator j Gx (φx + Real.pi)) (dy - dx) r +
     Complex.I * spaceSplittingStationaryRadialTerm K v j k dx dy
      (stationaryPhaseOperator j Gx φx) (stationaryPhaseOperator k Gy φy) (dx + dy) r -
     Complex.I * spaceSplittingStationaryRadialTerm K v j k dx dy
      (stationaryPhaseConjugateOperator j Gx (φx + Real.pi))
      (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) (-(dx + dy)) r)

theorem spaceSplittingStationaryProductTerms_eq_zero (K v T : ℕ) (dx dy : ℝ)
    (Gx Gy : ℝ → ℂ) (φx φy : ℝ) {r : ℝ} (hr : r ≤ 0) :
    spaceSplittingStationaryProductTerms K v T dx dy Gx Gy φx φy r = 0 := by
  have ha (m : ℤ) : spaceSplittingRadialAmplitude K v m r = 0 :=
    spaceSplittingRadialAmplitude_eq_zero K v m (fun h ↦ by
      have hs : (0 : ℝ) < (2 : ℝ) ^ v / 4 := by positivity
      linarith [h.1])
  simp [spaceSplittingStationaryProductTerms, spaceSplittingStationaryRadialTerm, ha]

theorem orthogonalityRadialAmplitude_mul_stationaryMain_product
    (K v T : ℕ) (bx by' : Plane → UnitCircle → ℝ) (x x' y y' : Plane)
    (hx : 0 < dist x x') (hy : 0 < dist y y') (r : ℝ) :
    orthogonalityRadialAmplitude K v r * spaceSplittingStationaryMain T bx r x x' *
        spaceSplittingStationaryMain T by' r y y' =
      (2 * Real.pi / Real.sqrt (dist x x' * dist y y') : ℝ) *
        spaceSplittingStationaryProductTerms K v T (dist x x') (dist y y')
          (builtSymbolPairAngularAmplitude bx bx x x')
          (builtSymbolPairAngularAmplitude by' by' y y')
          (radialAngle 0 (x - x')) (radialAngle 0 (y - y')) r := by
  by_cases hr : 0 < r
  · rw [spaceSplittingStationaryMain_eq_sum, spaceSplittingStationaryMain_eq_sum]
    unfold spaceSplittingStationaryProductTerms
    rw [mul_sum]
    simp only [mul_sum, sum_mul]
    conv_lhs => rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    convert spaceSplitting_stationary_product_term hr hx hy K v j k
      (stationaryPhaseOperator j (builtSymbolPairAngularAmplitude bx bx x x')
        (radialAngle 0 (x - x')))
      (stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude bx bx x x')
        (radialAngle 0 (x - x') + Real.pi))
      (stationaryPhaseOperator k (builtSymbolPairAngularAmplitude by' by' y y')
        (radialAngle 0 (y - y')))
      (stationaryPhaseConjugateOperator k (builtSymbolPairAngularAmplitude by' by' y y')
        (radialAngle 0 (y - y') + Real.pi)) using 1
    ring
  · have hr' := le_of_not_gt hr
    rw [spaceSplittingStationaryProductTerms_eq_zero K v T _ _ _ _ _ _ hr', mul_zero,
      orthogonalityRadialAmplitude_eq_zero K v (fun h ↦ by
        have hs : (0 : ℝ) < (2 : ℝ) ^ v / 4 := by positivity
        linarith [h.1]), zero_mul, zero_mul]

end FalconerThetaGauge
