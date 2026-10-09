module

public import FalconerThetaGauge.OrthogonalityKernelRadialBound
public import FalconerThetaGauge.ScheduledSymbolEnergy

/-! # Actual scheduled symbols give genuine angular two-pair cancellation -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman

theorem orthogonality_circle_source_decay {ρ : Measure Plane} {θ : ℝ} {N a p v : ℕ}
    (hpar : ParameterFacts θ N) (hpv : p ≤ v)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hcard : I.card ≤ N ^ 2 + 1) (hL : ∀ test ∈ I, test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {X P P' : Fin 2 → ℤ} (hP : dyadicCube p P ⊆ dyadicCube a X)
    (hP' : dyadicCube p P' ⊆ dyadicCube a X) {x x' : Plane}
    (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (arc : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (hfail : orthogonalityLinkThreshold p (tolerance θ N * N) <
      |inner ℝ (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ arc)) : Plane)
        (dyadicCellCenter p P - dyadicCellCenter p P')|)
    {r : ℝ} (hr : (2 : ℝ) ^ ((v : ℝ) - 2) ≤ r) :
    ‖∫ w, orthogonalityCircleKernel (8 * expansionCount θ N)
      (orthogonalityArcScale a p (tolerance θ N * N)) arc b x x' r w ∂circleArcLength‖ ≤
        2 * orthogonalityArcScale a p (tolerance θ N * N) *
          (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
  rw [integral_orthogonalityCircleKernel_eq_angular _ (orthogonalityArcScale_pos _ _ _)
    _ (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb)]
  exact orthogonality_angular_source_decay hpar hpv hgap hcard hL hlength hb hP hP'
    hx hx' arc hfail hr

theorem norm_orthogonalityTwoPairKernel_angular_source {ρ : Measure Plane} {θ : ℝ}
    {N a p v : ℕ} (hpar : ParameterFacts θ N) (hpv : p ≤ v)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {width : ℝ} {I : Finset ProfileScheduleTest} {L : ℕ}
    (hcard : I.card ≤ N ^ 2 + 1) (hL : ∀ test ∈ I, test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N) width
      (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {X P P' : Fin 2 → ℤ} (hP : dyadicCube p P ⊆ dyadicCube a X)
    (hP' : dyadicCube p P' ⊆ dyadicCube a X) {x x' : Plane}
    (hx : x ∈ dyadicCube p P) (hx' : x' ∈ dyadicCube p P')
    (y y' : Plane)
    (arc₁ arc₂ : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (hfail : orthogonalityLinkThreshold p (tolerance θ N * N) <
      |inner ℝ (circleQuarterTurn (unitCircleOfAngle (equalAngularCellCenter _ arc₁)) : Plane)
        (dyadicCellCenter p P - dyadicCellCenter p P')|) :
    ‖orthogonalityTwoPairKernel (8 * expansionCount θ N) v
      (orthogonalityArcScale a p (tolerance θ N * N)) arc₁ arc₂ b₁ b₂ x x' y y'‖ ≤
        64 * (4 : ℝ) ^ v * (2 * orthogonalityArcScale a p (tolerance θ N * N)) ^ 2 *
          (2 : ℝ) ^ (-(90 * (N : ℝ))) := by
  have hε := tolerance_pos θ (N := N) (by have := hpar.1; omega)
  have hT : 1 ≤ expansionCount θ N := Nat.ceil_pos.mpr (by positivity)
  apply norm_orthogonalityTwoPairKernel_le_of_angular_cancel hT (by omega)
    (orthogonalityArcScale_pos _ _ _) (orthogonalityArcScale_le_one _ _ _) (by positivity)
    arc₁ arc₂ (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₁)
    (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₂)
    (abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₁)
    (abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₂) x x' y y'
  intro r hr
  apply orthogonality_circle_source_decay hpar hpv hgap hcard hL hlength hb₁ hP hP'
    hx hx' arc₁ hfail
  have hlo := (tsupport_orthogonalityRadialAmplitude_subset (8 * expansionCount θ N) v hr).1
  have heq : (2 : ℝ) ^ ((v : ℝ) - 2) = (2 : ℝ) ^ v / 4 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
    norm_num
  rw [heq]
  exact hlo

end FalconerThetaGauge
