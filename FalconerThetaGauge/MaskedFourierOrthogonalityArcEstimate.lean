module

public import FalconerThetaGauge.MaskedFourierArcSchur
public import FalconerThetaGauge.MaskedFourierArcErrorBudget
public import FalconerThetaGauge.MaskedFourierArcSum
public import FalconerThetaGauge.OrthogonalityKernelCrossBound
public import FalconerThetaGauge.DistanceLinearizationMassDecomposition

/-! # The true orthogonality estimate on each smoothed pair of arcs -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem maskedFourierArcPairEnergy_le_orthogonality (ρ : Measure Plane)
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
    (X Y : Fin 2 → ℤ)
    (i j : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N)))) :
    let ℓ := orthogonalityArcScale a p (tolerance θ N * N)
    maskedFourierArcPairEnergy ρ ρ (dyadicCube a X) (dyadicCube a Y) b₁ b₂
        (8 * expansionCount θ N) v ℓ i j ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        12 * tolerance θ N)) *
        (∑ P ∈ (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y),
          maskedFourierArcPairEnergy ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂
            (8 * expansionCount θ N) v ℓ i j) +
      (64 * (4 : ℝ) ^ v * (2 * ℓ) ^ 2 * (2 : ℝ) ^ (-(90 * (N : ℝ)))) *
        (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 := by
  dsimp only
  let E := tolerance θ N * N
  let K := 8 * expansionCount θ N
  let ℓ := orthogonalityArcScale a p E
  let s := (symbolActiveCellDescendants ρ a p X K ℓ i b₁).product
    (symbolActiveCellDescendants ρ a p Y K ℓ j b₂)
  let linked := orthogonalityLinked p (orthogonalityLinkThreshold p E)
    (unitCircleOfAngle (equalAngularCellCenter _ i))
    (unitCircleOfAngle (equalAngularCellCenter _ j))
  let m := fun P : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
    ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)
  let Z := fun P : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
    maskedFourierArcPairAmplitude ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ K ℓ i j
  let C := 64 * (4 : ℝ) ^ v * (2 * ℓ) ^ 2 * (2 : ℝ) ^ (-(90 * (N : ℝ)))
  have hap := hag.trans hgp
  have hcross : ∀ P ∈ s, ∀ Q ∈ s, ¬linked P Q →
      |∫ z, inner ℝ (Z P z) (Z Q z) ∂maskedFourierJointMeasure K v| ≤ C * m P * m Q := by
    intro P hP Q hQ hnot
    obtain ⟨hP₁, hP₂⟩ := mem_product.mp hP
    obtain ⟨hQ₁, hQ₂⟩ := mem_product.mp hQ
    have hh := abs_integral_real_inner_maskedFourierArcPair_unlinked hpar hv hpv hw hgap
      hcard hL hlength hb₁ hb₂
      (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap (mem_filter.mp hP₁).1)
      (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap (mem_filter.mp hQ₁).1)
      (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap (mem_filter.mp hP₂).1)
      (dyadicCube_subset_of_mem_occupiedCellDescendants ρ hap (mem_filter.mp hQ₂).1) i j hnot
    convert hh using 1
    dsimp only [C, m, E, ℓ]
    ring
  have herror : (∑ P ∈ s, ∑ Q ∈ s,
      if linked P Q then 0 else
        |∫ z, inner ℝ (Z P z) (Z Q z) ∂maskedFourierJointMeasure K v|) ≤
      C * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 := by
    calc
      _ ≤ ∑ P ∈ s, ∑ Q ∈ s, if linked P Q then 0 else C * m P * m Q := by
        apply sum_le_sum
        intro P hP
        apply sum_le_sum
        intro Q hQ
        split_ifs with hlink
        · exact le_rfl
        · exact hcross P hP Q hQ hlink
      _ ≤ _ := sum_unlinked_mass_products_le s linked m
        (fun _ _ ↦ by dsimp [m]; positivity) (by dsimp [C]; positivity)
        (sum_symbolActiveCellPairs_mass_le ρ ρ hap X Y K ℓ i j b₁ b₂)
  have hs := maskedFourierArcPairEnergy_le_links ρ ρ hρ hρ hpar hreg hag hgp
    (hpv.trans hv) hancestor hlevels hsize level K (2 * expansionCount θ N) v (by omega)
    hwidth hordered htest hb₁
    (measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₂)
    (abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ (by omega) hb₂) X Y i j
  exact hs.trans (add_le_add
    (mul_le_mul_of_nonneg_left
      (sum_active_arc_energy_le_occupied ρ ρ a p X Y b₁ b₂ K v ℓ i j) (by positivity)) herror)

end FalconerThetaGauge
