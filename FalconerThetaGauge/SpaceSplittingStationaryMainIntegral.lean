module

public import FalconerThetaGauge.SpaceSplittingStationaryMainSum

/-! # Actual radial averaging of both circular stationary mains -/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace FalconerThetaGauge

theorem integrable_spaceSplittingStationaryProductTerms (K v T : ℕ) (dx dy : ℝ)
    (Gx Gy : ℝ → ℂ) (φx φy : ℝ) :
    Integrable (spaceSplittingStationaryProductTerms K v T dx dy Gx Gy φx φy) := by
  unfold spaceSplittingStationaryProductTerms
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  exact (((integrable_spaceSplittingStationaryRadialTerm K v j k dx dy _ _ _).add
    (integrable_spaceSplittingStationaryRadialTerm K v k j dy dx _ _ _)).add
      ((integrable_spaceSplittingStationaryRadialTerm K v j k dx dy _ _ _).const_mul _)).sub
        ((integrable_spaceSplittingStationaryRadialTerm K v j k dx dy _ _ _).const_mul _)

theorem integral_spaceSplittingStationaryProductTerms (K v T : ℕ) (dx dy : ℝ)
    (Gx Gy : ℝ → ℂ) (φx φy : ℝ) :
    (2 * Real.pi / Real.sqrt (dx * dy) : ℝ) *
        (∫ r : ℝ, spaceSplittingStationaryProductTerms K v T dx dy Gx Gy φx φy r) =
      spaceSplittingOppositeRadialSeries K v T dx dy Gx Gy φx φy +
        spaceSplittingEqualSignRadialSeries K v T dx dy Gx Gy φx φy := by
  let f (j k : ℕ) (r : ℝ) :=
    spaceSplittingStationaryRadialTerm K v j k dx dy
      (stationaryPhaseOperator j Gx φx)
      (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) (dx - dy) r +
    spaceSplittingStationaryRadialTerm K v k j dy dx
      (stationaryPhaseOperator k Gy φy)
      (stationaryPhaseConjugateOperator j Gx (φx + Real.pi)) (dy - dx) r +
    Complex.I * spaceSplittingStationaryRadialTerm K v j k dx dy
      (stationaryPhaseOperator j Gx φx) (stationaryPhaseOperator k Gy φy) (dx + dy) r -
    Complex.I * spaceSplittingStationaryRadialTerm K v j k dx dy
      (stationaryPhaseConjugateOperator j Gx (φx + Real.pi))
      (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) (-(dx + dy)) r
  have hi (j k : ℕ) : Integrable (f j k) := by
    exact (((integrable_spaceSplittingStationaryRadialTerm K v j k dx dy _ _ _).add
      (integrable_spaceSplittingStationaryRadialTerm K v k j dy dx _ _ _)).add
        ((integrable_spaceSplittingStationaryRadialTerm K v j k dx dy _ _ _).const_mul _)).sub
          ((integrable_spaceSplittingStationaryRadialTerm K v j k dx dy _ _ _).const_mul _)
  change (2 * Real.pi / Real.sqrt (dx * dy) : ℝ) *
    (∫ r : ℝ, ∑ j ∈ range T, ∑ k ∈ range T, f j k r) = _
  rw [integral_finsetSum (range T)
    (f := fun j r ↦ ∑ k ∈ range T, f j k r)
    (fun j _ ↦ integrable_finsetSum (range T) (fun k _ ↦ hi j k))]
  simp_rw [integral_finsetSum (range T) (fun k _ ↦ hi _ k)]
  unfold spaceSplittingOppositeRadialSeries spaceSplittingEqualSignRadialSeries
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  dsimp only [f]
  have h₁ := integrable_spaceSplittingStationaryRadialTerm K v j k dx dy
    (stationaryPhaseOperator j Gx φx)
    (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) (dx - dy)
  have h₂ := integrable_spaceSplittingStationaryRadialTerm K v k j dy dx
    (stationaryPhaseOperator k Gy φy)
    (stationaryPhaseConjugateOperator j Gx (φx + Real.pi)) (dy - dx)
  have h₃ := integrable_spaceSplittingStationaryRadialTerm K v j k dx dy
    (stationaryPhaseOperator j Gx φx) (stationaryPhaseOperator k Gy φy) (dx + dy)
  have h₄ := integrable_spaceSplittingStationaryRadialTerm K v j k dx dy
    (stationaryPhaseConjugateOperator j Gx (φx + Real.pi))
    (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) (-(dx + dy))
  have hsub := integral_sub ((h₁.add h₂).add (h₃.const_mul Complex.I))
    (h₄.const_mul Complex.I)
  have hadd₁ := integral_add (h₁.add h₂) (h₃.const_mul Complex.I)
  have hadd₂ := integral_add h₁ h₂
  simp only [Pi.add_apply] at hsub hadd₁ hadd₂
  rw [hsub, hadd₁, hadd₂, integral_const_mul, integral_const_mul]
  simp only [integral_spaceSplittingStationaryRadialTerm, spaceSplittingOppositeTerm]
  ring

theorem integral_orthogonalityRadialAmplitude_mul_stationaryMain_product
    (K v T : ℕ) (bx by' : Plane → UnitCircle → ℝ) (x x' y y' : Plane)
    (hx : 0 < dist x x') (hy : 0 < dist y y') :
    (∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        spaceSplittingStationaryMain T bx r x x' *
        spaceSplittingStationaryMain T by' r y y') =
      spaceSplittingOppositeRadialSeries K v T (dist x x') (dist y y')
        (builtSymbolPairAngularAmplitude bx bx x x')
        (builtSymbolPairAngularAmplitude by' by' y y')
        (radialAngle 0 (x - x')) (radialAngle 0 (y - y')) +
      spaceSplittingEqualSignRadialSeries K v T (dist x x') (dist y y')
        (builtSymbolPairAngularAmplitude bx bx x x')
        (builtSymbolPairAngularAmplitude by' by' y y')
        (radialAngle 0 (x - x')) (radialAngle 0 (y - y')) := by
  simp_rw [orthogonalityRadialAmplitude_mul_stationaryMain_product K v T bx by'
    x x' y y' hx hy]
  rw [integral_const_mul]
  exact integral_spaceSplittingStationaryProductTerms K v T _ _ _ _ _ _

end FalconerThetaGauge
