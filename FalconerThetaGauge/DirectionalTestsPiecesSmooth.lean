/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.DirectionalTestsPieces
public import FalconerThetaGauge.RegularFunctions

/-! # Exact piece products and angular smoothness of the assembled symbol -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem scheduledDirectionalFilter_symbol_eq (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (N : ℕ) (E : ℝ) (K : ℕ) (I : Finset ProfileScheduleTest) (hcard : I.card ≤ N ^ 2 + 1)
    (C : Set Plane) (hC : MeasurableSet C)
    (hcoverage : ∀ test ∈ I, C ⊆ cellUnion test.anchor (occupiedUnitCells ρ test.anchor))
    (x : Plane) (w : UnitCircle) :
    (scheduledDirectionalFilter ρ N E K I hcard C hC hcoverage).symbol x w =
      if x ∈ C then ∏ test ∈ I, scheduledTestSymbol ρ E test K x w else 0 := by
  change (if x ∈ C then
    ∏ i : Fin I.card, scheduledTestSymbol ρ E (I.equivFin.symm i).val K x w else 0) = _
  by_cases hx : x ∈ C
  · rw [ite_eq_left hx, ite_eq_left hx]
    calc
      _ = ∏ test : I, scheduledTestSymbol ρ E test.val K x w :=
        Fintype.prod_equiv I.equivFin.symm _ _ (fun _ => rfl)
      _ = ∏ test ∈ I, scheduledTestSymbol ρ E test K x w :=
        Finset.prod_coe_sort I (fun test => scheduledTestSymbol ρ E test K x w)
  · simp [hx]

theorem regularPieceDirectionalFilter_symbol_eq (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    (x : Plane) (w : UnitCircle) :
    let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t.val
    (regularPieceDirectionalFilter μ hpar K t).symbol x w =
      if x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val then
        ∏ test ∈ regularMeasurePieceTests ρ θ N,
          scheduledTestSymbol ρ (tolerance θ N * N) test K x w
      else 0 := by
  let : IsProbabilityMeasure (regularDyadicPartMeasure μ (tolerance θ N) N t.val) :=
    (regularDyadicPartMeasure_probability μ (tolerance θ N) (blockParameter θ N) N t.property).1
  unfold regularPieceDirectionalFilter
  exact scheduledDirectionalFilter_symbol_eq _ _ _ _ _ _ _ _ _ x w

/-- The global symbol on a piece is literally the product of that piece's source test list. -/
theorem regularDirectionalFilter_symbol_eq_piece_product (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    {x : Plane} (hx : x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val) (w : UnitCircle) :
    let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t.val
    (regularDirectionalFilter μ hpar K).symbol x w =
      ∏ test ∈ regularMeasurePieceTests ρ θ N,
        scheduledTestSymbol ρ (tolerance θ N * N) test K x w := by
  rw [regularDirectionalFilter_symbol_on_piece μ hpar K t hx,
    regularPieceDirectionalFilter_symbol_eq, ite_eq_left hx]

theorem contDiff_regularPieceDirectionalFilter_symbol_comp_angle (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    (x : Plane) :
    ContDiff ℝ ∞
      (fun α => (regularPieceDirectionalFilter μ hpar K t).symbol x (unitCircleOfAngle α)) := by
  simp_rw [regularPieceDirectionalFilter_symbol_eq]
  by_cases hx : x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val
  · simp only [ite_eq_left hx]
    apply contDiff_prod
    intro test _
    exact contDiff_scheduledTestSymbol_comp_angle _ _ test K x
  · simp only [ite_eq_right hx]
    exact contDiff_const

/-- Global angular smoothness follows from the actual disjoint piece partition. -/
theorem contDiff_regularDirectionalFilter_symbol_comp_angle (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) (K : ℕ)
    (x : Plane) :
    ContDiff ℝ ∞ (fun α => (regularDirectionalFilter μ hpar K).symbol x (unitCircleOfAngle α)) := by
  by_cases hx : x ∈ regularFilterCarrier μ θ N
  · obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    have heq : (fun α => (regularDirectionalFilter μ hpar K).symbol x (unitCircleOfAngle α)) =
        fun α => (regularPieceDirectionalFilter μ hpar K ⟨t, ht⟩).symbol x (unitCircleOfAngle α) :=
      funext (fun α => regularDirectionalFilter_symbol_on_piece μ hpar K ⟨t, ht⟩ hxt _)
    rw [heq]
    exact contDiff_regularPieceDirectionalFilter_symbol_comp_angle μ hpar K ⟨t, ht⟩ x
  · have heq : (fun α => (regularDirectionalFilter μ hpar K).symbol x (unitCircleOfAngle α)) =
        fun _ : ℝ => 0 := by
      ext α
      unfold FiniteDirectionalFilter.symbol carrierDirectionalSymbol
      rw [regularDirectionalFilter_carrier, ite_eq_right hx]
    rw [heq]
    exact contDiff_const

end FalconerThetaGauge
