module

public import FalconerThetaGauge.OrthogonalityFirstLinks

/-! # The actual occupied linked-cell graph has the source degree bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def activeLinkedColumns (ρ₁ ρ₂ : Measure Plane) (a g p : ℕ) (X : Fin 2 → ℤ)
    (E width : ℝ) (w₁ w₂ : UnitCircle) (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  ((activeLinkedFirstColumns ρ₁ a g p X E width (dyadicCellCenter p row.1) w₁).product
    (occupiedUnitCells ρ₂ p)).filter
      (fun col ↦ orthogonalityLinked p (orthogonalityLinkThreshold p E) w₁ w₂ row col)

theorem activeLinkedColumns_fiber_count_le (ρ₁ ρ₂ : Measure Plane)
    (a g p : ℕ) (X : Fin 2 → ℤ) {E : ℝ} (hE : 0 ≤ E) (width : ℝ)
    (w₁ w₂ : UnitCircle) (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) (P' : Fin 2 → ℤ) :
    (((activeLinkedColumns ρ₁ ρ₂ a g p X E width w₁ w₂ row).filter
      (fun col ↦ col.1 = P')).card : ℝ) ≤ 81 * (2 : ℝ) ^ (3 * E) := by
  let S := (activeLinkedColumns ρ₁ ρ₂ a g p X E width w₁ w₂ row).filter
    (fun col ↦ col.1 = P')
  have hc : S.card ≤
      (linkedSecondColumns ρ₂ p (orthogonalityLinkThreshold p E) w₁ w₂ row P').card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro col hcol
      obtain ⟨hcol₀, hfirst⟩ := mem_filter.mp hcol
      obtain ⟨hprod, hlink⟩ := mem_filter.mp hcol₀
      apply mem_filter.mpr
      refine ⟨(mem_product.mp hprod).2, ?_⟩
      have he : col = (P', col.2) := Prod.ext hfirst rfl
      rw [he] at hlink
      exact hlink
    · intro x hx y hy he
      apply Prod.ext
      · exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
      · exact he
  exact (Nat.cast_le.mpr hc).trans (linkedSecondColumns_count_le ρ₂ p hE w₁ w₂ row P')

theorem activeLinkedColumns_count_le (ρ₁ ρ₂ : Measure Plane) [IsProbabilityMeasure ρ₁]
    (hρ₁ : ρ₁ unitSquare = 1) {θ : ℝ} {N a g p : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ₁) (hag : a ≤ g) (hgp : g ≤ p)
    (hp : p ≤ N) (hgap : (g : ℝ) - a ≤ tolerance θ N * N)
    (X : Fin 2 → ℤ) {width : ℝ} (hwidth : 1 ≤ width) (w₁ w₂ : UnitCircle)
    (row : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    ((activeLinkedColumns ρ₁ ρ₂ a g p X (tolerance θ N * N) width w₁ w₂ row).card : ℝ) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ₁ N) p g p +
        12 * tolerance θ N)) := by
  let E := tolerance θ N * N
  let H := profileHeight (regularMeasureExcess ρ₁ N) p g p
  let S := activeLinkedColumns ρ₁ ρ₂ a g p X E width w₁ w₂ row
  let F := activeLinkedFirstColumns ρ₁ a g p X E width (dyadicCellCenter p row.1) w₁
  have hE₁₆ : 16 ≤ E := hpar.2.2.1.1
  have hE : 0 ≤ E := by linarith
  have hF : (F.card : ℝ) ≤ (2 : ℝ) ^ (N * (H + 8 * tolerance θ N)) :=
    activeLinkedFirstColumns_count_le ρ₁ hρ₁ hpar hreg hag hgp hp hgap X
      (dyadicCellCenter p row.1) w₁ hwidth
  have hf (P' : Fin 2 → ℤ) : ((S.filter (fun col ↦ col.1 = P')).card : ℝ) ≤
      81 * (2 : ℝ) ^ (3 * E) :=
    activeLinkedColumns_fiber_count_le ρ₁ ρ₂ a g p X hE width w₁ w₂ row P'
  have hc : (S.card : ℝ) ≤ (F.card : ℝ) * (81 * (2 : ℝ) ^ (3 * E)) := by
    apply finite_fiber_count_le_mul S F Prod.fst
    · intro col hcol
      exact (mem_product.mp (mem_filter.mp hcol).1).1
    · intro P' _
      convert hf P' using 1
      congr 2
      ext col
      simp only [mem_filter]
  have h81 : (81 : ℝ) ≤ (2 : ℝ) ^ E := by
    calc
      _ ≤ (2 : ℝ) ^ (16 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hE₁₆
  calc
    _ ≤ _ := hc
    _ ≤ (2 : ℝ) ^ (N * (H + 8 * tolerance θ N)) * (81 * (2 : ℝ) ^ (3 * E)) :=
      mul_le_mul_of_nonneg_right hF (by positivity)
    _ = 81 * (2 : ℝ) ^ (N * (H + 11 * tolerance θ N)) := by
      rw [mul_left_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      dsimp [E]
      ring
    _ ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ (N * (H + 11 * tolerance θ N)) :=
      mul_le_mul_of_nonneg_right h81 (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [E]
      ring

end FalconerThetaGauge
