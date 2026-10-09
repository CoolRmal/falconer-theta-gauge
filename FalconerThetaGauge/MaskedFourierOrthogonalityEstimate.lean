module

public import FalconerThetaGauge.MaskedFourierOrthogonalityArcEstimate

/-! # Source Estimate 7.6 for the literal built symbols and occupied dyadic descendants -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem mass_mul_maskedFourierEnergy_le_orthogonality (ρ : Measure Plane)
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
    (X Y : Fin 2 → ℤ) :
    (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) *
        maskedFourierEnergy ρ ρ (dyadicCube a X) (dyadicCube a Y) b₁ b₂
          (8 * expansionCount θ N) v ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        12 * tolerance θ N)) *
        (∑ P ∈ (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y),
          (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)) *
            maskedFourierEnergy ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂
              (8 * expansionCount θ N) v) +
      (2 : ℝ) ^ (-(80 * (N : ℝ))) *
        (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) := by
  let K := 8 * expansionCount θ N
  let ℓ := orthogonalityArcScale a p (tolerance θ N * N)
  let M := ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)
  let D := (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
    12 * tolerance θ N))
  let C := 64 * (4 : ℝ) ^ v * (2 * ℓ) ^ 2 * (2 : ℝ) ^ (-(90 * (N : ℝ)))
  let s := (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y)
  have hℓ : 0 < ℓ := orthogonalityArcScale_pos _ _ _
  have hb₁m := measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₁
  have hb₂m := measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₂
  have hb₁b := abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₁
  have hb₂b := abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₂
  have htot : M * maskedFourierEnergy ρ ρ (dyadicCube a X) (dyadicCube a Y) b₁ b₂ K v ≤
      D * (∑ i : Fin (angularPartitionCount ℓ), ∑ j : Fin (angularPartitionCount ℓ),
        ∑ P ∈ s, maskedFourierArcPairEnergy ρ ρ (dyadicCube p P.1) (dyadicCube p P.2)
          b₁ b₂ K v ℓ i j) + (angularPartitionCount ℓ : ℝ) ^ 2 * C * M ^ 2 := by
    calc
      _ = ∑ i : Fin (angularPartitionCount ℓ), ∑ j : Fin (angularPartitionCount ℓ),
          maskedFourierArcPairEnergy ρ ρ (dyadicCube a X) (dyadicCube a Y) b₁ b₂ K v ℓ i j :=
        (sum_maskedFourierArcPairEnergy ρ ρ _ _ hb₁m hb₂m hb₁b hb₂b K v hℓ).symm
      _ ≤ ∑ i : Fin (angularPartitionCount ℓ), ∑ j : Fin (angularPartitionCount ℓ),
          (D * (∑ P ∈ s, maskedFourierArcPairEnergy ρ ρ (dyadicCube p P.1)
            (dyadicCube p P.2) b₁ b₂ K v ℓ i j) + C * M ^ 2) := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        exact maskedFourierArcPairEnergy_le_orthogonality ρ hρ hpar hreg hag hgp hv hpv
          hancestor hw hgap hlevels hsize level hwidth hordered htest hcard hL hlength
          hb₁ hb₂ X Y i j
      _ = _ := by
        simp_rw [sum_add_distrib, ← mul_sum]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hdiag := sum_occupied_arc_energy_eq ρ ρ a p X Y hb₁m hb₂m hb₁b hb₂b K v hℓ
  change (∑ i : Fin (angularPartitionCount ℓ), ∑ j : Fin (angularPartitionCount ℓ),
    ∑ P ∈ s, _) = _ at hdiag
  rw [hdiag] at htot
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hM₁ : M ≤ 1 := by
    dsimp only [M]
    simpa only [one_mul] using mul_le_mul
      (measureReal_le_one (μ := ρ) (s := dyadicCube a X))
      (measureReal_le_one (μ := ρ) (s := dyadicCube a Y)) measureReal_nonneg (by norm_num)
  have herror : (angularPartitionCount ℓ : ℝ) ^ 2 * C * M ^ 2 ≤
      (2 : ℝ) ^ (-(80 * (N : ℝ))) * M := by
    calc
      _ ≤ (2 : ℝ) ^ (-(80 * (N : ℝ))) * M ^ 2 :=
        mul_le_mul_of_nonneg_right
          (orthogonality_total_arc_error_le (by have := hpar.1; omega) hv hℓ
            (orthogonalityArcScale_le_one _ _ _)) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  exact htot.trans (add_le_add le_rfl herror)

end FalconerThetaGauge
