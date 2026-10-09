module

public import FalconerThetaGauge.ScheduledSymbolBudget

/-! # The actual assembled `8T` filter inherits the literal S3 symbol budget on each piece -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

theorem scheduledWidthTestSymbol_two (ρ : Measure Plane) (E : ℝ)
    (test : ProfileScheduleTest) (K : ℕ) :
    scheduledWidthTestSymbol ρ E 2 test K = scheduledTestSymbol ρ E test K := rfl

theorem scheduledWidthMaskProduct_two (ρ : Measure Plane) (E : ℝ) (K : ℕ)
    (I : Finset ProfileScheduleTest) :
    scheduledWidthMaskProduct ρ E 2 K I = scheduledMaskProduct ρ E K I := rfl

theorem regularMeasurePieceTests_nonempty (ρ : Measure Plane) (θ : ℝ) (N : ℕ) :
    (regularMeasurePieceTests ρ θ N).Nonempty :=
  ⟨⟨.tube, regularMeasureEntryDepth ρ θ N, 0⟩,
    Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl)⟩

/-- The filter uses the same actual finite convolution product as the zero-order class element. -/
theorem regularDirectionalFilter_symbol_isDerivativeRegular_eight (μ : Measure Plane)
    [IsProbabilityMeasure μ] {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    {T : ℕ} (hT : 1 ≤ T)
    (t : {t // t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N})
    {L : ℕ}
    (hL : ∀ test ∈ regularMeasurePieceTests
      (regularDyadicPartMeasure μ (tolerance θ N) N t.val) θ N, test.length ≤ L)
    {x : Plane} (hx : x ∈ regularDyadicPartCarrier μ (tolerance θ N) N t.val) :
    let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t.val
    IsDerivativeRegular 1
      (scheduledSymbolScale T (tolerance θ N * N) (regularMeasurePieceTests ρ θ N) L) (6 * T)
      (fun α ↦ ((regularDirectionalFilter μ hpar (8 * T)).symbol x (unitCircleOfAngle α) : ℂ)) := by
  let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t.val
  have heq : (fun α ↦ (regularDirectionalFilter μ hpar (8 * T)).symbol x
      (unitCircleOfAngle α)) = fun α ↦ ScheduledSymbolData.maskProduct.symbol ρ
        (tolerance θ N * N) 2 (8 * T) (regularMeasurePieceTests ρ θ N) x
          (unitCircleOfAngle α) := by
    ext α
    rw [regularDirectionalFilter_symbol_eq_piece_product μ hpar (8 * T) t hx,
      ScheduledSymbolData.maskProduct_symbol]
    rfl
  have hcomplex := congrArg (fun f : ℝ → ℝ ↦ fun α ↦ (f α : ℂ)) heq
  rw [hcomplex]
  exact ScheduledSymbolData.maskProduct.isDerivativeRegular ρ hT _ _ _
    (regularMeasurePieceTests_nonempty ρ θ N) hL
    (by simp [ScheduledSymbolData.maskProduct_order]) x

end FalconerThetaGauge
