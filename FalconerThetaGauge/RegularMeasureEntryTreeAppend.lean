module

public import FalconerThetaGauge.RegularMeasureEntryTreeLevels

/-! # Literal weights and mask levels after appending an induction transition -/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

namespace ProfileMoveChain

variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)
    (u : ProfileChainState) (move : ProfileChainMove A q N δ (chain.state chain.length) u)

theorem append_state_final : (chain.append u move).state (chain.append u move).length = u := by
  simp only [append, show ¬chain.length + 1 ≤ chain.length by omega, ite_false]

theorem append_levelIncrement_before {i : ℕ} (hi : i < chain.length) :
    (chain.append u move).levelIncrement i = chain.levelIncrement i := by
  simp only [levelIncrement, append, hi, show i < chain.length + 1 by omega,
    dite_eq_left]
  congr 1 <;> simp [show i ≤ chain.length by omega, show i + 1 ≤ chain.length by omega]

theorem append_levelIncrement_last :
    (chain.append u move).levelIncrement chain.length = move.levelIncrement := by
  simp only [levelIncrement, append, show chain.length < chain.length + 1 by omega,
    Nat.lt_irrefl, dite_eq_left, dite_false]
  congr 1 <;> simp [show ¬chain.length + 1 ≤ chain.length by omega]

theorem append_maskLevel (initial : ℕ) :
    (chain.append u move).maskLevel initial = chain.maskLevel initial + move.levelIncrement := by
  unfold maskLevel
  change initial + ∑ i ∈ range (chain.length + 1),
    (chain.append u move).levelIncrement i = _
  rw [sum_range_succ, append_levelIncrement_last]
  rw [Finset.sum_congr rfl (fun i hi ↦ chain.append_levelIncrement_before u move
    (mem_range.mp hi))]
  omega

theorem append_multiplier_before (ε : ℝ) {i : ℕ} (hi : i < chain.length) :
    (chain.append u move).multiplier ε i = chain.multiplier ε i := by
  simp only [multiplier, append, hi, show i < chain.length + 1 by omega,
    dite_eq_left]
  congr 1 <;> simp [show i ≤ chain.length by omega, show i + 1 ≤ chain.length by omega]

theorem append_multiplier_last (ε : ℝ) :
    (chain.append u move).multiplier ε chain.length = move.upperMultiplier ε := by
  simp only [multiplier, append, show chain.length < chain.length + 1 by omega,
    Nat.lt_irrefl, dite_eq_left, dite_false]
  congr 1 <;> simp [show ¬chain.length + 1 ≤ chain.length by omega]

theorem append_multiplierProduct (ε : ℝ) :
    (chain.append u move).multiplierProduct ε =
      chain.multiplierProduct ε * move.upperMultiplier ε := by
  unfold multiplierProduct
  change (∏ i ∈ range (chain.length + 1), (chain.append u move).multiplier ε i) = _
  rw [prod_range_succ, append_multiplier_last]
  rw [Finset.prod_congr rfl (fun i hi ↦ chain.append_multiplier_before u move ε
    (mem_range.mp hi))]

theorem multiplierProduct_nonneg (ε : ℝ) : 0 ≤ chain.multiplierProduct ε := by
  unfold multiplierProduct
  apply prod_nonneg
  intro i hi
  rw [multiplier_eq _ _ (mem_range.mp hi)]
  exact (chain.step i (mem_range.mp hi)).upperMultiplier_nonneg ε

end ProfileMoveChain

end FalconerThetaGauge
