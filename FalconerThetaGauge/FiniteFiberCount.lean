module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-! # Actual finite fiber counts with real uniform bounds -/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

theorem finite_fiber_count_le_mul {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → κ)
    (hmap : ∀ i ∈ s, f i ∈ t) {B : ℝ}
    (hf : ∀ j ∈ t, ((s.filter (fun i ↦ f i = j)).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ (t.card : ℝ) * B := by
  have he := card_eq_sum_card_fiberwise (f := f) (s := s) (t := t) hmap
  rw [he, Nat.cast_sum]
  calc
    _ ≤ ∑ _j ∈ t, B := sum_le_sum hf
    _ = _ := by simp

end FalconerThetaGauge
