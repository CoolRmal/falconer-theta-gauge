module

public import FalconerThetaGauge.SpaceSplittingOppositeTerms
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The actual two opposite stationary signs give the distance-collision kernel -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

def spaceSplittingOppositeRadialSeries (K v T : ℕ) (dx dy : ℝ)
    (Gx Gy : ℝ → ℂ) (φx φy : ℝ) : ℂ :=
  (2 * Real.pi / Real.sqrt (dx * dy) : ℝ) *
    ∑ j ∈ range T, ∑ k ∈ range T,
      (spaceSplittingOppositeTerm K v j k dx dy
        (stationaryPhaseOperator j Gx φx) (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) +
       spaceSplittingOppositeTerm K v k j dy dx
        (stationaryPhaseOperator k Gy φy) (stationaryPhaseConjugateOperator j Gx (φx + Real.pi)))

theorem norm_stationaryPhaseOperator_pair_scale {G : ℝ → ℂ} {M : ℝ} {T j : ℕ}
    (hG : IsDerivativeRegular 1 (2 * M) (6 * T) G) (hj : j < T) (φ : ℝ) :
    ‖stationaryPhaseOperator j G φ‖ ≤ (400 * j * M ^ 2) ^ j := by
  have h := norm_stationaryPhaseOperator_le_of_regular hG (by omega : 2 * j ≤ 6 * T) φ
  convert h using 1
  ring

theorem norm_stationaryPhaseConjugateOperator_pair_scale {G : ℝ → ℂ} {M : ℝ} {T j : ℕ}
    (hG : IsDerivativeRegular 1 (2 * M) (6 * T) G) (hj : j < T) (φ : ℝ) :
    ‖stationaryPhaseConjugateOperator j G φ‖ ≤ (400 * j * M ^ 2) ^ j := by
  have h := norm_stationaryPhaseConjugateOperator_le_of_regular hG
    (by omega : 2 * j ≤ 6 * T) φ
  convert h using 1
  ring

/-- The literal opposite-sign expansion obeys the source's `C < 2²⁵` kernel bound. -/
theorem norm_spaceSplittingOppositeRadialSeries_le {K v T : ℕ} (hK : 2 ≤ K)
    {dx dy M : ℝ} (hdx : 0 < dx) (hdy : 0 < dy) {Gx Gy : ℝ → ℂ}
    (hGx : IsDerivativeRegular 1 (2 * M) (6 * T) Gx)
    (hGy : IsDerivativeRegular 1 (2 * M) (6 * T) Gy)
    (hxscale : 1600 * T * M ^ 2 / ((2 : ℝ) ^ v * dx) ≤ 1 / 4)
    (hyscale : 1600 * T * M ^ 2 / ((2 : ℝ) ^ v * dy) ≤ 1 / 4) (φx φy : ℝ) :
    ‖spaceSplittingOppositeRadialSeries K v T dx dy Gx Gy φx φy‖ ≤
      (2 : ℝ) ^ (25 : ℕ) * (2 : ℝ) ^ v / Real.sqrt (dx * dy) /
        (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2 := by
  let S : ℝ := ∑ j ∈ range T, ∑ k ∈ range T,
    ((j : ℝ) + k + 2) ^ 2 * (1 / (4 : ℝ)) ^ (j + k)
  have hS : 2 * S ≤ 100 := two_stationary_order_double_geometric_sum_le_hundred T
  have hs : 0 < (2 : ℝ) ^ v := by positivity
  have hsqrt : 0 < Real.sqrt (dx * dy) := Real.sqrt_pos.2 (mul_pos hdx hdy)
  have hden : 0 < (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2 := by positivity
  have hterm (j : ℕ) (hj : j ∈ range T) (k : ℕ) (hk : k ∈ range T) :
      ‖spaceSplittingOppositeTerm K v j k dx dy
          (stationaryPhaseOperator j Gx φx)
          (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) +
        spaceSplittingOppositeTerm K v k j dy dx
          (stationaryPhaseOperator k Gy φy)
          (stationaryPhaseConjugateOperator j Gx (φx + Real.pi))‖ ≤
      (2 * 50176 * (2 : ℝ) ^ v / (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) *
        (((j : ℝ) + k + 2) ^ 2 * (1 / (4 : ℝ)) ^ (j + k)) := by
    have hj' := mem_range.1 hj
    have hk' := mem_range.1 hk
    have h₁ := norm_spaceSplittingOppositeTerm_le hK hdx hdy hj'.le hk'.le
      (norm_stationaryPhaseOperator_pair_scale hGx hj' φx)
      (norm_stationaryPhaseConjugateOperator_pair_scale hGy hk' (φy + Real.pi))
      hxscale hyscale
    have h₂ := norm_spaceSplittingOppositeTerm_le hK hdy hdx hk'.le hj'.le
      (norm_stationaryPhaseOperator_pair_scale hGy hk' φy)
      (norm_stationaryPhaseConjugateOperator_pair_scale hGx hj' (φx + Real.pi))
      hyscale hxscale
    have habs : |dy - dx| = |dx - dy| := abs_sub_comm _ _
    rw [habs, add_comm (k : ℝ) (j : ℝ), Nat.add_comm k j] at h₂
    apply (norm_add_le _ _).trans (add_le_add h₁ h₂) |>.trans_eq
    ring
  have hsum : ‖∑ j ∈ range T, ∑ k ∈ range T,
      (spaceSplittingOppositeTerm K v j k dx dy
        (stationaryPhaseOperator j Gx φx) (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) +
       spaceSplittingOppositeTerm K v k j dy dx
        (stationaryPhaseOperator k Gy φy)
        (stationaryPhaseConjugateOperator j Gx (φx + Real.pi)))‖ ≤
      100 * 50176 * (2 : ℝ) ^ v / (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2 := by
    calc
      _ ≤ ∑ j ∈ range T, ∑ k ∈ range T,
          ‖spaceSplittingOppositeTerm K v j k dx dy
              (stationaryPhaseOperator j Gx φx)
              (stationaryPhaseConjugateOperator k Gy (φy + Real.pi)) +
            spaceSplittingOppositeTerm K v k j dy dx
              (stationaryPhaseOperator k Gy φy)
              (stationaryPhaseConjugateOperator j Gx (φx + Real.pi))‖ := by
        apply (norm_sum_le _ _).trans
        exact sum_le_sum fun j _ ↦ norm_sum_le _ _
      _ ≤ ∑ j ∈ range T, ∑ k ∈ range T,
          (2 * 50176 * (2 : ℝ) ^ v / (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) *
            (((j : ℝ) + k + 2) ^ 2 * (1 / (4 : ℝ)) ^ (j + k)) := by
        exact sum_le_sum fun j hj ↦ sum_le_sum fun k hk ↦ hterm j hj k hk
      _ = (50176 * (2 : ℝ) ^ v / (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) * (2 * S) := by
        simp only [← mul_sum]
        dsimp [S]
        ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hS (by positivity :
          0 ≤ 50176 * (2 : ℝ) ^ v / (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) using 1
        ring
  have hconstant : 2 * Real.pi * (100 * 50176) ≤ (2 : ℝ) ^ (25 : ℕ) := by
    nlinarith [Real.pi_lt_d2]
  unfold spaceSplittingOppositeRadialSeries
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (mul_pos (by norm_num) Real.pi_pos) hsqrt)]
  calc
    _ ≤ (2 * Real.pi / Real.sqrt (dx * dy)) *
        (100 * 50176 * (2 : ℝ) ^ v / (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 * Real.pi * (100 * 50176)) *
        ((2 : ℝ) ^ v / Real.sqrt (dx * dy) /
          (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) := by ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_right hconstant (by positivity :
        0 ≤ (2 : ℝ) ^ v / Real.sqrt (dx * dy) /
          (1 + (2 : ℝ) ^ v * |dx - dy|) ^ 2) using 1
      ring

end FalconerThetaGauge
