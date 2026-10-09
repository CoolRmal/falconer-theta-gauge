/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntrySchedule

/-!
# Actual split and origin gains

The constructed split points supply the minimum plateaux that pay the costs
of Moves 1–3. Every positive-cost child has the literal `40q` length margin.
-/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

/-- The rounded tolerance numerator is no larger than the rounded block length. -/
theorem toleranceCount_le_blockCount_of_parameterFacts {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N) : toleranceCount θ N ≤ blockCount θ N := by
  rcases hpar with ⟨hN₄, _, _, _, hP4⟩
  rcases hP4 with ⟨_, hκβ, hβsmall, _, hεκ, _, _, _⟩
  have hN : 0 < N := by omega
  have hκ := blockParameter_pos θ hN
  have hκsmall : blockParameter θ N ≤ 1 / 10000 := hκβ.trans hβsmall
  have hε : tolerance θ N ≤ blockParameter θ N := by
    nlinarith
  have hcount := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) N)
  rw [tolerance_mul_scale θ hN, blockParameter_mul_scale θ hN] at hcount
  exact_mod_cast hcount

/-- Move 1: an actual right split pays its right-interval height. -/
theorem profileSplitPoint_right_budget_gain {A : ℕ → ℝ} {q N a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a)
    (hright : a + t < 2 * profileSplitPoint A q N a t) :
    50 * q < profileSplitPoint A q N a t - a ∧
      profileHeight A (profileSplitPoint A q N a t) (profileSplitPoint A q N a t) t ≤
        profileBudget A q a (profileSplitPoint A q N a t) - profileBudget A q a t := by
  have hp := profileSplitPoint_bounds (A := A) hq ht hlong
  have hlength : 50 * q < profileSplitPoint A q N a t - a := by omega
  refine ⟨hlength, profileBudget_pays_right_split (by omega) (by omega) ?_⟩
  intro n hn hnp
  exact profileSplitPoint_le_on_left hq ht hlong (by omega) hnp

/-- Move 2: an actual left split pays its left-interval height even after the high-shell shift. -/
theorem profileSplitPoint_left_budget_gain {A : ℕ → ℝ} {q N a t v δ : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hlong : 100 * q < t - a) (hδ : δ ≤ q)
    (hleft : 2 * profileSplitPoint A q N a t ≤ a + t) (hvlo : t - δ < v) (hvt : v ≤ t) :
    40 * q < v - profileSplitPoint A q N a t ∧
      profileHeight A (profileSplitPoint A q N a t) a (profileSplitPoint A q N a t) ≤
        profileBudget A q (profileSplitPoint A q N a t) v - profileBudget A q a t := by
  have hp := profileSplitPoint_bounds (A := A) hq ht hlong
  have hlength : 40 * q < v - profileSplitPoint A q N a t := by omega
  refine ⟨hlength, profileBudget_pays_left_split (by omega) (by omega) hvt ?_⟩
  intro n hpn hnv
  exact profileSplitPoint_le_on_right hq ht hlong hpn (by omega)

/-- Move 3: the actual origin of a longest test pays its height whenever that cost is positive. -/
theorem profileOrigin_left_budget_gain {A : ℕ → ℝ} {q N a v a' t' L δ : ℕ}
    (hq : 0 < q) (ht' : t' ≤ N) (horigin : 100 * q < t' - a')
    (hlong : 100 * q < v - a) (hδ : δ ≤ q) (hL : v - a ≤ 2 * L)
    (hstart : a < profileSplitPoint A q N a' t')
    (hleft : a' + L ≤ profileSplitPoint A q N a' t')
    (hright : profileSplitPoint A q N a' t' + L ≤ t') (hend : t' ≤ v + δ)
    {cost : ℝ} (hcost : cost ≤
      profileHeight A (profileSplitPoint A q N a' t') a (profileSplitPoint A q N a' t')) :
    40 * q < v - profileSplitPoint A q N a' t' ∧
      cost ≤ profileBudget A q (profileSplitPoint A q N a' t') v - profileBudget A q a v := by
  let p := profileSplitPoint A q N a' t'
  have hlength : 40 * q < v - p := by dsimp [p]; omega
  have hmargin : p + 10 * q ≤ v := by omega
  refine ⟨hlength, ?_⟩
  by_cases hc : cost ≤ 0
  · have hmono := profileBudget_mono (A := A) hstart.le hmargin (le_refl v)
    linarith
  · have hpositive : 0 < profileHeight A p a p := lt_of_lt_of_le (lt_of_not_ge hc) hcost
    obtain ⟨m, ham, hmp, hmin⟩ := exists_profileMinimum_eq (A := A) hstart.le
    have hAm : A m < A p := by unfold profileHeight at hpositive; rw [hmin] at hpositive; linarith
    have hmleft : m < a' + 2 * q := by
      by_contra hm
      have hplateau := profileSplitPoint_le_on_left hq ht' horigin (le_of_not_gt hm) hmp
      exact hAm.not_ge hplateau
    have hvend : v < t' + 2 * q := by omega
    have hplateau : ∀ n, p ≤ n → n ≤ v - 10 * q → A p ≤ A n := by
      intro n hpn hnv
      exact profileSplitPoint_le_on_right hq ht' horigin hpn (by omega)
    exact hcost.trans (profileBudget_pays_left_split hstart.le hmargin (le_refl v) hplateau)

end FalconerThetaGauge
