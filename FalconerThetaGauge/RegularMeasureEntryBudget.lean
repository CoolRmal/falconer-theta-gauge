/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryActual

/-!
# The finite budget pays interval gains

Interval inclusion gives the zero-cost monotonicity in Lemma 8.6. The
Lipschitz estimate bounds each budget near any chosen depth, and actual
minimum plateaux pay the left- and right-split heights.
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

/-- A attained profile minimum equals a specified value when that value is a lower bound. -/
theorem profileMinimum_eq_of_point_min {A : ℕ → ℝ} {a b p : ℕ}
    (hap : a ≤ p) (hpb : p ≤ b) (hA : ∀ n, a ≤ n → n ≤ b → A p ≤ A n) :
    profileMinimum A a b = A p :=
  le_antisymm (profileMinimum_le hap hpb) (le_profileMinimum (hap.trans hpb) hA)

/-- The trimmed budgets increase under inclusion of intervals, proving Lemma 8.6(b). -/
theorem profileBudget_mono {A : ℕ → ℝ} {q a b c d : ℕ}
    (hac : a ≤ c) (hmargin : c + 10 * q ≤ d) (hdb : d ≤ b) :
    profileBudget A q a b ≤ profileBudget A q c d := by
  unfold profileBudget
  exact add_le_add
    (profileMinimum_mono hac (by omega) (Nat.sub_le_sub_right hdb _))
    (profileMinimum_mono (by omega) hmargin hdb)

/-- The budget lies within `20q/N` above twice the profile at any depth in the interval. -/
theorem profileBudget_le_near_point {A : ℕ → ℝ} {N q a b n : ℕ}
    (hN : 0 < N) (hmargin : a + 10 * q ≤ b) (han : a ≤ n) (hnb : n ≤ b)
    (hLip : ∀ u v : ℕ, |A u - A v| ≤ |(u : ℝ) - v| / N) :
    profileBudget A q a b ≤ 2 * A n + 20 * (q : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  let m₁ := min n (b - 10 * q)
  let m₂ := max n (a + 10 * q)
  have ham₁ : a ≤ m₁ := by dsimp [m₁]; omega
  have hm₁b : m₁ ≤ b - 10 * q := min_le_right _ _
  have ham₂ : a + 10 * q ≤ m₂ := le_max_right _ _
  have hm₂b : m₂ ≤ b := by dsimp [m₂]; omega
  have hnear₁ : |(m₁ : ℝ) - n| ≤ 10 * (q : ℝ) := by
    have hmn : m₁ ≤ n := min_le_left _ _
    have hgap : n ≤ m₁ + 10 * q := by dsimp [m₁]; omega
    have hmn' : (m₁ : ℝ) ≤ n := by exact_mod_cast hmn
    have hgap' : (n : ℝ) ≤ m₁ + 10 * q := by exact_mod_cast hgap
    rw [abs_of_nonpos (sub_nonpos.mpr hmn')]
    linarith
  have hnear₂ : |(m₂ : ℝ) - n| ≤ 10 * (q : ℝ) := by
    have hnm : n ≤ m₂ := le_max_left _ _
    have hgap : m₂ ≤ n + 10 * q := by dsimp [m₂]; omega
    have hnm' : (n : ℝ) ≤ m₂ := by exact_mod_cast hnm
    have hgap' : (m₂ : ℝ) ≤ n + 10 * q := by exact_mod_cast hgap
    rw [abs_of_nonneg (sub_nonneg.mpr hnm')]
    linarith
  have hdiff₁ := (le_abs_self (A m₁ - A n)).trans
    ((hLip m₁ n).trans (div_le_div_of_nonneg_right hnear₁ hN'.le))
  have hdiff₂ := (le_abs_self (A m₂ - A n)).trans
    ((hLip m₂ n).trans (div_le_div_of_nonneg_right hnear₂ hN'.le))
  have hmin₁ := profileMinimum_le (A := A) ham₁ hm₁b
  have hmin₂ := profileMinimum_le (A := A) ham₂ hm₂b
  unfold profileBudget
  rw [show 20 * (q : ℝ) / N = 2 * (10 * (q : ℝ) / N) by ring]
  linarith

/-- The actual excess budget satisfies the manuscript's `22κ` bound in Lemma 8.6(c). -/
theorem regularMeasureExcess_budget_le_near_point
    (ρ : MeasureTheory.Measure Plane) [MeasureTheory.IsProbabilityMeasure ρ]
    (hρ : ρ GaugeSeparatedMeasures.unitSquare = 1) (θ : ℝ) {N a b n : ℕ}
    (hN : 0 < N) (hmargin : a + 10 * blockCount θ N ≤ b) (han : a ≤ n) (hnb : n ≤ b) :
    profileBudget (regularMeasureExcess ρ N) (blockCount θ N) a b ≤
      2 * regularMeasureExcess ρ N n + 22 * blockParameter θ N := by
  have h := profileBudget_le_near_point hN hmargin han hnb
    (regularMeasureExcess_lipschitz ρ hρ hN)
  have heq : 20 * (blockCount θ N : ℝ) / N = 20 * blockParameter θ N := by
    unfold blockParameter
    ring
  rw [heq] at h
  have hκ := blockParameter_pos θ hN
  linarith

/-- A minimum plateau in a right split pays the exact right-interval height. -/
theorem profileBudget_pays_right_split {A : ℕ → ℝ} {q a p t : ℕ}
    (hmargin : a + 10 * q ≤ p) (hpt : p ≤ t)
    (hplateau : ∀ n, a + 10 * q ≤ n → n ≤ p → A p ≤ A n) :
    profileHeight A p p t ≤ profileBudget A q a p - profileBudget A q a t := by
  have hleft := profileMinimum_mono (A := A) (le_refl a)
    (by omega : a ≤ p - 10 * q) (Nat.sub_le_sub_right hpt (10 * q))
  have hright := profileMinimum_mono (A := A) hmargin hpt (le_refl t)
  have hnew := profileMinimum_eq_of_point_min hmargin (le_refl p) hplateau
  unfold profileHeight profileBudget
  rw [hnew]
  linarith

/-- A minimum plateau in a left split pays the exact left-interval height. -/
theorem profileBudget_pays_left_split {A : ℕ → ℝ} {q a p v t : ℕ}
    (hap : a ≤ p) (hmargin : p + 10 * q ≤ v) (hvt : v ≤ t)
    (hplateau : ∀ n, p ≤ n → n ≤ v - 10 * q → A p ≤ A n) :
    profileHeight A p a p ≤ profileBudget A q p v - profileBudget A q a t := by
  have hleft := profileMinimum_mono (A := A) (le_refl a) hap
    (show p ≤ t - 10 * q by omega)
  have hright := profileMinimum_mono (A := A) (show a + 10 * q ≤ p + 10 * q by omega)
    hmargin hvt
  have hnew := profileMinimum_eq_of_point_min (le_refl p) (by omega : p ≤ v - 10 * q) hplateau
  unfold profileHeight profileBudget
  rw [hnew]
  linarith

end FalconerThetaGauge
