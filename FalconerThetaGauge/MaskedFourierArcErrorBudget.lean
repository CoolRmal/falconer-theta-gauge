module

public import FalconerThetaGauge.MaskedFourierActiveCells

/-! # Actual active-cell mass sums and the total small-arc cancellation budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

theorem angularPartitionCount_mul_double_width_le {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) :
    (angularPartitionCount ℓ : ℝ) * (2 * ℓ) ≤ 16 := by
  have h := (le_div_iff₀ hℓ).mp (angularPartitionCount_le hℓ hℓ₁)
  linarith

/-- Summing all actual arc-pair kernel constants still gives the source terminal error. -/
theorem orthogonality_total_arc_error_le {N v : ℕ} (hN : 2 ≤ N) (hv : v ≤ N)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) :
    (angularPartitionCount ℓ : ℝ) ^ 2 *
      (64 * (4 : ℝ) ^ v * (2 * ℓ) ^ 2 * (2 : ℝ) ^ (-(90 * (N : ℝ)))) ≤
        (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
  have hM := angularPartitionCount_mul_double_width_le hℓ hℓ₁
  have hM₀ : 0 ≤ (angularPartitionCount ℓ : ℝ) * (2 * ℓ) := by positivity
  have hV : (4 : ℝ) ^ v ≤ (4 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hv
  have hpow : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * (N : ℝ)) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, ← Real.rpow_natCast]
    norm_num
  have hC : (64 : ℝ) * 16 ^ (2 : ℕ) = (2 : ℝ) ^ (14 : ℝ) := by norm_num
  calc
    _ = 64 * ((angularPartitionCount ℓ : ℝ) * (2 * ℓ)) ^ 2 *
        (4 : ℝ) ^ v * (2 : ℝ) ^ (-(90 * (N : ℝ))) := by ring
    _ ≤ 64 * (16 : ℝ) ^ 2 * (4 : ℝ) ^ N *
        (2 : ℝ) ^ (-(90 * (N : ℝ))) := by gcongr
    _ = (2 : ℝ) ^ (14 - 88 * (N : ℝ)) := by
      rw [hpow, hC, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith)

theorem sum_symbolActiveCellDescendants_mass_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a p : ℕ} (hap : a ≤ p) (X : Fin 2 → ℤ) (K : ℕ) (ℓ : ℝ)
    (i : Fin (angularPartitionCount ℓ)) (b : Plane → UnitCircle → ℝ) :
    (∑ P ∈ symbolActiveCellDescendants ρ a p X K ℓ i b, ρ.real (dyadicCube p P)) ≤
      ρ.real (dyadicCube a X) := by
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun _ _ _ ↦ measureReal_nonneg)).trans (sum_occupiedCellDescendants_le ρ hap X)

theorem sum_symbolActiveCellPairs_mass_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) (K : ℕ) (ℓ : ℝ) (i j : Fin (angularPartitionCount ℓ))
    (b₁ b₂ : Plane → UnitCircle → ℝ) :
    (∑ P ∈ (symbolActiveCellDescendants ρ₁ a p X K ℓ i b₁).product
        (symbolActiveCellDescendants ρ₂ a p Y K ℓ j b₂),
      ρ₁.real (dyadicCube p P.1) * ρ₂.real (dyadicCube p P.2)) ≤
        ρ₁.real (dyadicCube a X) * ρ₂.real (dyadicCube a Y) := by
  have he := sum_product
    (symbolActiveCellDescendants ρ₁ a p X K ℓ i b₁)
    (symbolActiveCellDescendants ρ₂ a p Y K ℓ j b₂)
    (fun P ↦ ρ₁.real (dyadicCube p P.1) * ρ₂.real (dyadicCube p P.2))
  apply he.trans_le
  dsimp only [Prod.fst, Prod.snd]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  exact mul_le_mul
    (sum_symbolActiveCellDescendants_mass_le ρ₁ hap X K ℓ i b₁)
    (sum_symbolActiveCellDescendants_mass_le ρ₂ hap Y K ℓ j b₂)
    (sum_nonneg fun _ _ ↦ measureReal_nonneg) measureReal_nonneg

theorem sum_unlinked_mass_products_le {ι : Type*} (s : Finset ι)
    (linked : ι → ι → Prop) [DecidableRel linked] (m : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) {C M : ℝ} (hC : 0 ≤ C)
    (hs : (∑ i ∈ s, m i) ≤ M) :
    (∑ i ∈ s, ∑ j ∈ s, if linked i j then 0 else C * m i * m j) ≤ C * M ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, C * m i * m j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      split_ifs
      · exact mul_nonneg (mul_nonneg hC (hm i hi)) (hm j hj)
      · exact le_rfl
    _ = C * (∑ i ∈ s, m i) ^ 2 := by
      simp_rw [← mul_sum]
      rw [← sum_mul, ← mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sum_nonneg hm) hs 2) hC

end FalconerThetaGauge
