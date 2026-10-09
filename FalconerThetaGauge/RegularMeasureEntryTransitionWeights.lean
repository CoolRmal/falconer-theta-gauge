module

public import FalconerThetaGauge.RegularMeasureEntryTreeLevels

/-! # Table 1 coefficients determined by the actual parent and child states -/

@[expose] public section

noncomputable section

open scoped Classical

namespace FalconerThetaGauge

/-- The coefficient of an actual child, expressed without choosing transition proofs. -/
def profileTransitionMultiplier (A : ℕ → ℝ) (q N : ℕ) (ε : ℝ)
    (s u : ProfileChainState) : ℝ :=
  match s with
  | .discrepancy a t =>
      let p := profileSplitPoint A q N a t
      if a + t < 2 * p then (2 : ℝ) ^ (N * (profileHeight A p p t + 7 * ε))
      else if u.isFourier then (2 : ℝ) ^ (N * (profileHeight A p a p + 13 * ε)) else 320
  | .fourier b e a v =>
      if v - a ≤ 2 * profileLongestTestLength A q N b e a then
        (2 : ℝ) ^ (N * (profileHeight A u.start a u.start + 12 * ε))
      else if u.isFourier then 81 ^ 2 else (2 : ℝ) ^ (90 : ℝ)

/-- A discrepancy child advances the level once; a Fourier child keeps it. -/
def profileTransitionLevelIncrement (u : ProfileChainState) : ℕ :=
  if u.isFourier then 0 else 1

theorem profileTransitionMultiplier_nonneg (A : ℕ → ℝ) (q N : ℕ) (ε : ℝ)
    (s u : ProfileChainState) : 0 ≤ profileTransitionMultiplier A q N ε s u := by
  cases s <;> unfold profileTransitionMultiplier <;>
    split_ifs <;> positivity

theorem ProfileChainMove.upperMultiplier_eq_transition {A : ℕ → ℝ} {q N δ : ℕ}
    {s u : ProfileChainState} (ε : ℝ) (move : ProfileChainMove A q N δ s u) :
    move.upperMultiplier ε = profileTransitionMultiplier A q N ε s u := by
  cases move with
  | linearize a t hlong hright =>
    simp only [ProfileChainMove.upperMultiplier, ProfileChainMove.budgetCost,
      profileTransitionMultiplier, hright, ite_true]
  | lowFrequency a t hlong hleft =>
    simp only [ProfileChainMove.upperMultiplier, profileTransitionMultiplier,
      show ¬a + t < 2 * profileSplitPoint A q N a t by omega, ite_false,
      ProfileChainState.isFourier, Bool.false_eq_true]
  | highFrequency a t v hlong hleft hvlo hvhi =>
    simp only [ProfileChainMove.upperMultiplier, ProfileChainMove.budgetCost,
      profileTransitionMultiplier,
      show ¬a + t < 2 * profileSplitPoint A q N a t by omega, ite_false,
      ProfileChainState.isFourier, ite_true]
  | refine b e a v hlong test htest hlargest hlarge =>
    simp only [ProfileChainMove.upperMultiplier, ProfileChainMove.budgetCost,
      profileTransitionMultiplier, ProfileChainState.start,
      show v - a ≤ 2 * profileLongestTestLength A q N b e a by omega, ite_true]
  | near b e a v hlong hsmall =>
    simp only [ProfileChainMove.upperMultiplier, profileTransitionMultiplier,
      show ¬v - a ≤ 2 * profileLongestTestLength A q N b e a by omega, ite_false,
      ProfileChainState.isFourier, ite_true]
  | far b e a v n hlong hsmall hnlo hnhi hnv =>
    simp only [ProfileChainMove.upperMultiplier, profileTransitionMultiplier,
      show ¬v - a ≤ 2 * profileLongestTestLength A q N b e a by omega, ite_false,
      ProfileChainState.isFourier, Bool.false_eq_true]

theorem ProfileChainMove.levelIncrement_eq_transition {A : ℕ → ℝ} {q N δ : ℕ}
    {s u : ProfileChainState} (move : ProfileChainMove A q N δ s u) :
    move.levelIncrement = profileTransitionLevelIncrement u := by
  cases move <;> rfl

end FalconerThetaGauge
