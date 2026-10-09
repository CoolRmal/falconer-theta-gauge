module

public import FalconerThetaGauge.MaskedFourierActiveCells
public import FalconerThetaGauge.MaskedFourierArcEnergy
public import FalconerThetaGauge.ScheduledSymbolEnergy

/-! # Integrated Schur for the genuine active-cell graph and actual arc amplitudes -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The true arc energy satisfies Schur with the derived link degree and integrated errors. -/
theorem maskedFourierArcPairEnergy_le_links (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1)
    {θ : ℝ} {N a g p : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ₁) (hag : a ≤ g) (hgp : g ≤ p)
    (hp : p ≤ N) (hgap : (g : ℝ) - a ≤ tolerance θ N * N)
    {L : ℕ} (hL : 0 < L) (hsize : (L : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8)
    (level K k₀ v : ℕ) (hk : k₀ ≤ K) (hwidth : 1 ≤ directionalLevelWidth L (level + 1))
    {I : Finset ProfileScheduleTest} (hordered : ScheduledTestsOrdered I)
    (htest : (⟨.tube, p, g⟩ : ProfileScheduleTest) ∈ I)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ₁ (tolerance θ N * N)
      (directionalLevelWidth L level) K I k₀)
    (hb₂ : Measurable (uncurry b₂)) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (X Y : Fin 2 → ℤ)
    (i j : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N)))) :
    let ℓ := orthogonalityArcScale a p (tolerance θ N * N)
    let s := (symbolActiveCellDescendants ρ₁ a p X K ℓ i b₁).product
      (symbolActiveCellDescendants ρ₂ a p Y K ℓ j b₂)
    let linked := orthogonalityLinked p (orthogonalityLinkThreshold p (tolerance θ N * N))
      (unitCircleOfAngle (equalAngularCellCenter _ i))
      (unitCircleOfAngle (equalAngularCellCenter _ j))
    maskedFourierArcPairEnergy ρ₁ ρ₂ (dyadicCube a X) (dyadicCube a Y) b₁ b₂ K v ℓ i j ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ₁ N) p g p +
        12 * tolerance θ N)) *
        (∑ P ∈ s, maskedFourierArcPairEnergy ρ₁ ρ₂ (dyadicCube p P.1)
          (dyadicCube p P.2) b₁ b₂ K v ℓ i j) +
      ∑ P ∈ s, ∑ Q ∈ s, if linked P Q then 0 else
        |∫ z, inner ℝ
          (maskedFourierArcPairAmplitude ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2)
            b₁ b₂ K ℓ i j z)
          (maskedFourierArcPairAmplitude ρ₁ ρ₂ (dyadicCube p Q.1) (dyadicCube p Q.2)
            b₁ b₂ K ℓ i j z) ∂maskedFourierJointMeasure K v| := by
  dsimp only
  let ℓ := orthogonalityArcScale a p (tolerance θ N * N)
  let s := (symbolActiveCellDescendants ρ₁ a p X K ℓ i b₁).product
    (symbolActiveCellDescendants ρ₂ a p Y K ℓ j b₂)
  let linked := orthogonalityLinked p (orthogonalityLinkThreshold p (tolerance θ N * N))
    (unitCircleOfAngle (equalAngularCellCenter _ i))
    (unitCircleOfAngle (equalAngularCellCenter _ j))
  let Z := fun P : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
    maskedFourierArcPairAmplitude ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ K ℓ i j
  have hℓ : 0 < ℓ := orthogonalityArcScale_pos a p _
  have hb₁m := measurable_of_mem_scheduledSymbolClass _ _ _ _ _ _ hb₁
  have hb₁b := abs_le_one_of_mem_scheduledSymbolClass _ _ _ _ _ hk hb₁
  have hdegree : ∀ P ∈ s,
      ((s.filter (linked P)).card : ℝ) ≤
        (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ₁ N) p g p +
          12 * tolerance θ N)) := by
    intro P _hP
    exact symbolActiveLinkedColumns_count_le ρ₁ ρ₂ hρ₁ hpar hreg hag hgp hp hgap
      hL hsize level K k₀ hwidth hordered htest hb₁ b₂ X Y i j P
  have hcross : ∀ P ∈ s, ∀ Q ∈ s,
      Integrable (fun z ↦ inner ℝ (Z P z) (Z Q z)) (maskedFourierJointMeasure K v) := by
    intro P _ Q _
    exact integrable_real_inner_of_memLp_two
      (memLp_maskedFourierArcPairAmplitude ρ₁ ρ₂ _ _ hb₁m hb₂ hb₁b hbound₂ K v hℓ i j)
      (memLp_maskedFourierArcPairAmplitude ρ₁ ρ₂ _ _ hb₁m hb₂ hb₁b hbound₂ K v hℓ i j)
  have he : maskedFourierArcPairAmplitude ρ₁ ρ₂ (dyadicCube a X) (dyadicCube a Y)
      b₁ b₂ K ℓ i j = fun z ↦ ∑ P ∈ s, Z P z := by
    funext z
    exact maskedFourierArcPairAmplitude_active ρ₁ ρ₂ hρ₁ hρ₂ (hag.trans hgp) X Y
      hb₁m hb₂ hb₁b hbound₂ K ℓ i j z
  have hh := integral_norm_sum_sq_le_graph_schur (maskedFourierJointMeasure K v) s linked
    (fun {_ _} h ↦ orthogonalityLinked_symm p _ _ _ h) Z hdegree hcross
  change maskedFourierArcPairEnergy ρ₁ ρ₂ _ _ b₁ b₂ K v ℓ i j ≤ _
  unfold maskedFourierArcPairEnergy
  rw [he]
  exact hh

end FalconerThetaGauge
