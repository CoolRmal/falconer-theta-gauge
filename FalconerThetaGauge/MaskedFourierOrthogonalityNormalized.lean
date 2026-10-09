module

public import FalconerThetaGauge.MaskedFourierOrthogonalityEstimate

/-! # The exact mass-normalized orthogonality recurrence on genuine occupied cells -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem maskedFourierEnergy_le_orthogonality (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N a g p v : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hag : a ≤ g) (hgp : g ≤ p) (hv : v ≤ N) (hpv : p ≤ v)
    (hancestor : (g : ℝ) - a ≤ tolerance θ N * N)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {levels : ℕ} (hlevels : 0 < levels)
    (hsize : (levels : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8)
    (level : ℕ) (hwidth : 1 ≤ directionalLevelWidth levels (level + 1))
    {I : Finset ProfileScheduleTest} (hordered : ScheduledTestsOrdered I)
    (htest : (⟨.tube, p, g⟩ : ProfileScheduleTest) ∈ I)
    {L : ℕ} (hcard : I.card ≤ N ^ 2 + 1) (hL : ∀ test ∈ I, test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels level) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ (tolerance θ N * N)
      (directionalLevelWidth levels level) (8 * expansionCount θ N) I (2 * expansionCount θ N))
    {X Y : Fin 2 → ℤ} (hX : X ∈ occupiedUnitCells ρ a)
    (hY : Y ∈ occupiedUnitCells ρ a) :
    maskedFourierEnergy ρ ρ (dyadicCube a X) (dyadicCube a Y) b₁ b₂
        (8 * expansionCount θ N) v ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        12 * tolerance θ N)) *
        (∑ P ∈ (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y),
          (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)) /
            (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) *
            maskedFourierEnergy ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂
              (8 * expansionCount θ N) v) + (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
  have hm : 0 < ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) :=
    mul_pos (mem_filter.mp hX).2 (mem_filter.mp hY).2
  have hh := mass_mul_maskedFourierEnergy_le_orthogonality ρ hρ hpar hreg hag hgp hv hpv
    hancestor hw hgap hlevels hsize level hwidth hordered htest hcard hL hlength hb₁ hb₂ X Y
  apply (mul_le_mul_iff_right₀ hm).mp
  convert hh using 1
  rw [mul_add, mul_left_comm (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y))]
  congr 1
  · congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro P _
    have hXne : ρ.real (dyadicCube a X) ≠ 0 := ne_of_gt (mem_filter.mp hX).2
    have hYne : ρ.real (dyadicCube a Y) ≠ 0 := ne_of_gt (mem_filter.mp hY).2
    field_simp [hXne, hYne]
  · ring

end FalconerThetaGauge
