/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryChainCosts

/-!
# Telescoping the actual costs through a finite chain

Every prefix with a sufficiently long final interval is paid by its budget
increase. For an arbitrarily short leaf, the last positive-cost move still
has a `40q` margin; this yields the exact leaf-point bound needed in Section 8.5.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

namespace ProfileMoveChain

variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)

/-- The actual transition's budget cost, extended by zero outside the chain. -/
def cost (i : ℕ) : ℝ :=
  if hi : i < chain.length then (chain.step i hi).budgetCost else 0

theorem cost_eq {i : ℕ} (hi : i < chain.length) :
    chain.cost i = (chain.step i hi).budgetCost := by
  simp only [cost, hi, dite_eq_left]

/-- The sum of the actual height costs on the finite chain. -/
def totalCost : ℝ := ∑ i ∈ range chain.length, chain.cost i

theorem cost_nonneg (hq : 0 < q) (hδq : δ ≤ q) (i : ℕ) : 0 ≤ chain.cost i := by
  by_cases hi : i < chain.length
  · rw [chain.cost_eq hi]
    exact (chain.step i hi).budgetCost_nonneg hq (chain.state_valid hq hδq (by omega))
  · simp [cost, hi]

/-- Exact telescoping of costs for every prefix whose final interval has length `10q`. -/
theorem prefix_cost_le_budget_gain (hq : 0 < q) (hδq : δ ≤ q) {m : ℕ}
    (hm : m ≤ chain.length)
    (hmargin : 10 * q ≤ (chain.state m).finish - (chain.state m).start) :
    ∑ i ∈ range m, chain.cost i ≤
      profileBudget A q (chain.state m).start (chain.state m).finish -
        profileBudget A q (chain.state 0).start (chain.state 0).finish := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m < chain.length := by omega
    have hparent := (chain.step m hm').long
    have hprevious := ih (by omega) (by omega)
    have hstep := (chain.step m hm').budgetCost_paid hq hδq
      (chain.state_valid hq hδq (by omega)) hmargin
    rw [Finset.sum_range_succ, chain.cost_eq hm']
    linarith

/-- The cost of an actual chain is controlled at every point of its final interval, even
when that final interval is shorter than `10q`. -/
theorem totalCost_le_near_final_point (hq : 0 < q) (hδq : δ ≤ q) (hN : 0 < N)
    (hroot : 10 * q ≤ (chain.state 0).finish - (chain.state 0).start) {n : ℕ}
    (hnlo : (chain.state chain.length).start ≤ n)
    (hnhi : n ≤ (chain.state chain.length).finish)
    (hLip : ∀ u v : ℕ, |A u - A v| ≤ |(u : ℝ) - v| / N) :
    chain.totalCost ≤ 2 * A n + 20 * (q : ℝ) / N -
      profileBudget A q (chain.state 0).start (chain.state 0).finish := by
  cases hm : chain.length with
  | zero =>
    have hpoint := profileBudget_le_near_point (A := A) (q := q)
      (a := (chain.state 0).start) (b := (chain.state 0).finish) hN (by omega)
      (by simpa only [hm] using hnlo) (by simpa only [hm] using hnhi) hLip
    simp only [totalCost, hm, Finset.range_zero, Finset.sum_empty]
    linarith
  | succ m =>
    have hm' : m < chain.length := by omega
    have hparent := (chain.step m hm').long
    have hprefix := chain.prefix_cost_le_budget_gain hq hδq (m := m) (by omega) (by omega)
    by_cases hcost : 0 < (chain.step m hm').budgetCost
    · have hchild := ((chain.step m hm').positive_budgetCost_paid hq hδq
        (chain.state_valid hq hδq (by omega)) hcost).1
      have hfull := chain.prefix_cost_le_budget_gain hq hδq (m := chain.length)
        (le_refl _) (by simpa only [hm] using (by omega :
          10 * q ≤ (chain.state (m + 1)).finish - (chain.state (m + 1)).start))
      have hpoint := profileBudget_le_near_point (q := q) hN
        (by rw [hm]; omega) hnlo hnhi hLip
      exact hfull.trans (by linarith)
    · have hzero : chain.cost m = 0 := by
        rw [chain.cost_eq hm']
        exact le_antisymm (le_of_not_gt hcost)
          ((chain.step m hm').budgetCost_nonneg hq (chain.state_valid hq hδq (by omega)))
      have hstarts := chain.starts_monotone hq hδq (i := m) (j := chain.length)
        (by omega) (le_refl _)
      have hends := chain.ends_antitone hq hδq (i := m) (j := chain.length)
        (by omega) (le_refl _)
      have hpoint := profileBudget_le_near_point (q := q) hN (by omega)
        (hstarts.trans hnlo) (hnhi.trans hends) hLip
      unfold totalCost
      rw [hm, Finset.sum_range_succ, hzero, add_zero]
      linarith

/-- The actual regular-measure chain has the manuscript's `22κ` leaf budget bound. -/
theorem totalCost_le_excess_final_point (ρ : MeasureTheory.Measure Plane)
    [MeasureTheory.IsProbabilityMeasure ρ] (hρ : ρ GaugeSeparatedMeasures.unitSquare = 1)
    {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N)
    (chain : ProfileMoveChain (regularMeasureExcess ρ N)
      (blockCount θ N) N (toleranceCount θ N))
    (hroot : 10 * blockCount θ N ≤ (chain.state 0).finish - (chain.state 0).start) {n : ℕ}
    (hnlo : (chain.state chain.length).start ≤ n)
    (hnhi : n ≤ (chain.state chain.length).finish) :
    chain.totalCost ≤ 2 * regularMeasureExcess ρ N n + 22 * blockParameter θ N -
      profileBudget (regularMeasureExcess ρ N) (blockCount θ N)
        (chain.state 0).start (chain.state 0).finish := by
  have hN : 0 < N := by have := hpar.1; omega
  have hκ := blockParameter_pos θ hN
  have h := chain.totalCost_le_near_final_point (blockCount_pos θ hN)
    (toleranceCount_le_blockCount_of_parameterFacts hpar) hN hroot hnlo hnhi
    (regularMeasureExcess_lipschitz ρ hρ hN)
  have heq : 20 * (blockCount θ N : ℝ) / N = 20 * blockParameter θ N := by
    unfold blockParameter
    ring
  rw [heq] at h
  linarith

end ProfileMoveChain

end FalconerThetaGauge
