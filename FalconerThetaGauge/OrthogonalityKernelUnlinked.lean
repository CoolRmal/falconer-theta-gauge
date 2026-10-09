module

public import FalconerThetaGauge.OrthogonalityKernelRadialSource

/-! # Genuine unlinked two-pair cancellation for the scheduled symbols and actual cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman

theorem norm_orthogonalityTwoPairKernel_unlinked {ρ : Measure Plane} {θ : ℝ}
    {N a p v : ℕ} (hpar : ParameterFacts θ N) (hv : v ≤ N) (hpv : p ≤ v)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hcard : I.card ≤ N ^ 2 + 1) (hL : ∀ test ∈ I, test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {X Y P P' Q Q' : Fin 2 → ℤ}
    (hP : dyadicCube p P ⊆ dyadicCube a X) (hP' : dyadicCube p P' ⊆ dyadicCube a X)
    (hQ : dyadicCube p Q ⊆ dyadicCube a Y) (hQ' : dyadicCube p Q' ⊆ dyadicCube a Y)
    {x x' y y' : Plane} (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (hy : y ∈ dyadicCube p Q) (hy' : y' ∈ dyadicCube p Q')
    (i j : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (hnot : ¬orthogonalityLinked p (orthogonalityLinkThreshold p (tolerance θ N * N))
      (unitCircleOfAngle (equalAngularCellCenter _ i))
      (unitCircleOfAngle (equalAngularCellCenter _ j)) (P, Q) (P', Q')) :
    ‖orthogonalityTwoPairKernel (8 * expansionCount θ N) v
      (orthogonalityArcScale a p (tolerance θ N * N)) i j b₁ b₂ x x' y y'‖ ≤
        64 * (4 : ℝ) ^ v * (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
          (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
  by_cases h₁ : |inner ℝ
      (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ i)) : Plane)
      (dyadicCellCenter p P - dyadicCellCenter p P')| ≤
        orthogonalityLinkThreshold p (tolerance θ N * N)
  · by_cases h₂ : |inner ℝ
        (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ j)) : Plane)
        (dyadicCellCenter p Q - dyadicCellCenter p Q')| ≤
          orthogonalityLinkThreshold p (tolerance θ N * N)
    · apply norm_orthogonalityTwoPairKernel_radial_source hpar hv hw
        (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₁)
        (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₂)
        (abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₁)
        (abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₂)
        hP hP' hQ hQ' hx hx' hy hy' i j
      exact lt_of_not_ge (fun h₃ ↦ hnot ⟨h₁, h₂, h₃⟩)
    · rw [orthogonalityTwoPairKernel_swap]
      exact norm_orthogonalityTwoPairKernel_angular_source hpar hpv hgap hcard hL hlength
        hb₂ hb₁ hQ hQ' hy hy' x x' j i (lt_of_not_ge h₂)
  · exact norm_orthogonalityTwoPairKernel_angular_source hpar hpv hgap hcard hL hlength
      hb₁ hb₂ hP hP' hx hx' y y' i j (lt_of_not_ge h₁)

end FalconerThetaGauge
