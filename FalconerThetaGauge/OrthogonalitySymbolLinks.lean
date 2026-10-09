module

public import FalconerThetaGauge.OrthogonalityLinkDegree
public import FalconerThetaGauge.ScheduledSymbolSupport

/-! # Few links for the genuine nonzero built-symbol columns and actual smoothed arcs -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def symbolActiveCellDescendants (ρ : Measure Plane) (a p : ℕ) (X : Fin 2 → ℤ)
    (K : ℕ) (ℓ : ℝ) (arc : Fin (angularPartitionCount ℓ))
    (b : Plane → UnitCircle → ℝ) : Finset (Fin 2 → ℤ) :=
  (occupiedCellDescendants ρ a p X).filter (fun P ↦ ∃ x ∈ dyadicCube p P,
    ∃ w : UnitCircle, equalArcCutoff K ℓ arc w ≠ 0 ∧ b x w ≠ 0)

theorem linked_symbolActiveCell_mem_firstColumns (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {E : ℝ} {L : ℕ} (hL : 0 < L) (hsize : (L : ℝ) ≤ (2 : ℝ) ^ E / 8)
    (level K k₀ : ℕ) {I : Finset ProfileScheduleTest} (hordered : ScheduledTestsOrdered I)
    {a g p : ℕ} (htest : (⟨.tube, p, g⟩ : ProfileScheduleTest) ∈ I)
    {b : Plane → UnitCircle → ℝ}
    (hb : b ∈ scheduledSymbolClass ρ E (directionalLevelWidth L level) K I k₀)
    (X : Fin 2 → ℤ) (arc : Fin (angularPartitionCount (orthogonalityArcScale a p E)))
    (w₂ : UnitCircle) (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) {P Q : Fin 2 → ℤ}
    (hP : P ∈ symbolActiveCellDescendants ρ a p X K (orthogonalityArcScale a p E) arc b)
    (hlink : orthogonalityLinked p (orthogonalityLinkThreshold p E)
      (unitCircleOfAngle (equalAngularCellCenter
        (angularPartitionCount (orthogonalityArcScale a p E)) arc)) w₂ row (P, Q)) :
    P ∈ activeLinkedFirstColumns ρ a g p X E (directionalLevelWidth L (level + 1))
      (dyadicCellCenter p row.1) (unitCircleOfAngle (equalAngularCellCenter
        (angularPartitionCount (orthogonalityArcScale a p E)) arc)) := by
  obtain ⟨hPdesc, x, hx, w, hχ, hbx⟩ := mem_filter.mp hP
  apply mem_filter.mpr
  refine ⟨hPdesc, ?_, w, ?_, ?_⟩
  · rw [← neg_sub (dyadicCellCenter p row.1) (dyadicCellCenter p P),
      inner_neg_right, abs_neg]
    exact hlink.1
  · exact equalArcCutoff_norm_sub_center_le K (orthogonalityArcScale_pos a p E) arc hχ
  · have hpass := ne_zero_implies_next_passing_of_mem_scheduledSymbolClass ρ E hL hsize
      level K k₀ I hordered hb hbx _ htest
    have hPocc : P ∈ occupiedUnitCells ρ p :=
      mem_filter.mpr ⟨(mem_filter.mp hPdesc).1, (mem_filter.mp hPdesc).2.2⟩
    have hdir := (mem_scheduledPassingPinSet_on_cell ρ E
      (directionalLevelWidth L (level + 1)) ⟨.tube, p, g⟩ hPocc hx w).mp hpass
    exact hdir

def symbolActiveLinkedColumns (ρ₁ ρ₂ : Measure Plane) (a p : ℕ) (X Y : Fin 2 → ℤ)
    (E : ℝ) (K : ℕ)
    (arc₁ arc₂ : Fin (angularPartitionCount (orthogonalityArcScale a p E)))
    (b₁ b₂ : Plane → UnitCircle → ℝ) (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  ((symbolActiveCellDescendants ρ₁ a p X K (orthogonalityArcScale a p E) arc₁ b₁).product
    (symbolActiveCellDescendants ρ₂ a p Y K (orthogonalityArcScale a p E) arc₂ b₂)).filter
      (fun col ↦ orthogonalityLinked p (orthogonalityLinkThreshold p E)
        (unitCircleOfAngle (equalAngularCellCenter
          (angularPartitionCount (orthogonalityArcScale a p E)) arc₁))
        (unitCircleOfAngle (equalAngularCellCenter
          (angularPartitionCount (orthogonalityArcScale a p E)) arc₂)) row col)

theorem symbolActiveLinkedColumns_count_le (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsFiniteMeasure ρ₂] (hρ₁ : ρ₁ unitSquare = 1)
    {θ : ℝ} {N a g p : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ₁) (hag : a ≤ g) (hgp : g ≤ p)
    (hp : p ≤ N) (hgap : (g : ℝ) - a ≤ tolerance θ N * N)
    {L : ℕ} (hL : 0 < L) (hsize : (L : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8)
    (level K k₀ : ℕ) (hwidth : 1 ≤ directionalLevelWidth L (level + 1))
    {I : Finset ProfileScheduleTest} (hordered : ScheduledTestsOrdered I)
    (htest : (⟨.tube, p, g⟩ : ProfileScheduleTest) ∈ I)
    {b₁ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ₁ (tolerance θ N * N)
      (directionalLevelWidth L level) K I k₀) (b₂ : Plane → UnitCircle → ℝ)
    (X Y : Fin 2 → ℤ)
    (arc₁ arc₂ : Fin (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))))
    (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    ((symbolActiveLinkedColumns ρ₁ ρ₂ a p X Y (tolerance θ N * N) K
      arc₁ arc₂ b₁ b₂ row).card : ℝ) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ₁ N) p g p +
        12 * tolerance θ N)) := by
  let w₁ := unitCircleOfAngle (equalAngularCellCenter
    (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))) arc₁)
  let w₂ := unitCircleOfAngle (equalAngularCellCenter
    (angularPartitionCount (orthogonalityArcScale a p (tolerance θ N * N))) arc₂)
  have hsub : symbolActiveLinkedColumns ρ₁ ρ₂ a p X Y (tolerance θ N * N) K
      arc₁ arc₂ b₁ b₂ row ⊆ activeLinkedColumns ρ₁ ρ₂ a g p X (tolerance θ N * N)
        (directionalLevelWidth L (level + 1)) w₁ w₂ row := by
    intro col hcol
    obtain ⟨hprod, hlink⟩ := mem_filter.mp hcol
    obtain ⟨hP, hQ⟩ := mem_product.mp hprod
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_, ?_⟩, hlink⟩
    · exact linked_symbolActiveCell_mem_firstColumns ρ₁ hL hsize level K k₀ hordered
        htest hb₁ X arc₁ w₂ row hP hlink
    · have hdesc := mem_filter.mp (mem_filter.mp hQ).1
      exact mem_filter.mpr ⟨hdesc.1, hdesc.2.2⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (activeLinkedColumns_count_le ρ₁ ρ₂ hρ₁ hpar hreg hag hgp hp hgap X hwidth w₁ w₂ row)

end FalconerThetaGauge
