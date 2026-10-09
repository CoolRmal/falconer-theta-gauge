/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureExcessCount
public import FalconerThetaGauge.ParameterBudgets
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Actual finite interval minima, heights and budgets

These definitions retain the discrete depth intervals and the integer margins
`10q` in Definitions 5.9 and 8.1.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The attained minimum of a profile on a nonempty finite depth interval. -/
def profileMinimum (A : ℕ → ℝ) (a b : ℕ) : ℝ :=
  if h : a ≤ b then (Finset.Icc a b).inf' (Finset.nonempty_Icc.mpr h) A else 0

/-- The height `kₚ[a,b] = A(p) - min_[a,b] A`. -/
def profileHeight (A : ℕ → ℝ) (p a b : ℕ) : ℝ := A p - profileMinimum A a b

/-- The budget `V([a,b])` with the literal integer block margin `10q`. -/
def profileBudget (A : ℕ → ℝ) (q a b : ℕ) : ℝ :=
  profileMinimum A a (b - 10 * q) + profileMinimum A (a + 10 * q) b

theorem profileMinimum_le {A : ℕ → ℝ} {a b n : ℕ} (han : a ≤ n) (hnb : n ≤ b) :
    profileMinimum A a b ≤ A n := by
  rw [profileMinimum, dite_eq_left (han.trans hnb)]
  exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨han, hnb⟩)

theorem le_profileMinimum {A : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) {c : ℝ}
    (hA : ∀ n, a ≤ n → n ≤ b → c ≤ A n) : c ≤ profileMinimum A a b := by
  rw [profileMinimum, dite_eq_left hab]
  exact Finset.le_inf' _ _ (fun n hn ↦ hA n (Finset.mem_Icc.mp hn).1
    (Finset.mem_Icc.mp hn).2)

theorem exists_profileMinimum_eq {A : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) :
    ∃ n, a ≤ n ∧ n ≤ b ∧ profileMinimum A a b = A n := by
  rw [profileMinimum, dite_eq_left hab]
  obtain ⟨n, hn, hA⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_Icc.mpr hab) A
  exact ⟨n, (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2, hA⟩

theorem profileHeight_nonneg {A : ℕ → ℝ} {p a b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) :
    0 ≤ profileHeight A p a b := sub_nonneg.mpr (profileMinimum_le hap hpb)

theorem profileMinimum_mono {A : ℕ → ℝ} {a b c d : ℕ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    profileMinimum A a b ≤ profileMinimum A c d :=
  le_profileMinimum hcd (fun _ hcn hnd ↦ profileMinimum_le (hac.trans hcn) (hnd.trans hdb))

theorem profileHeight_le_of_bounds {A : ℕ → ℝ} {p a b : ℕ} (hab : a ≤ b)
    {lo hi : ℝ} (hlo : ∀ n, a ≤ n → n ≤ b → lo ≤ A n) (hhi : A p ≤ hi) :
    profileHeight A p a b ≤ hi - lo := by
  have hmin := le_profileMinimum hab hlo
  unfold profileHeight
  linarith

/-- A profile between `-κ` and `1` has budget between `-2κ` and `2`. -/
theorem profileBudget_bounds {A : ℕ → ℝ} {q a b N : ℕ} {κ : ℝ}
    (hmargin : a + 10 * q ≤ b) (hb : b ≤ N)
    (hA : ∀ n ≤ N, -κ ≤ A n ∧ A n ≤ 1) :
    -2 * κ ≤ profileBudget A q a b ∧ profileBudget A q a b ≤ 2 := by
  have hlo₁ : -κ ≤ profileMinimum A a (b - 10 * q) :=
    le_profileMinimum (by omega) (fun n _ hn ↦ (hA n (by omega)).1)
  have hlo₂ : -κ ≤ profileMinimum A (a + 10 * q) b :=
    le_profileMinimum hmargin (fun n _ hn ↦ (hA n (hn.trans hb)).1)
  have hhi₁ : profileMinimum A a (b - 10 * q) ≤ 1 :=
    (profileMinimum_le (by omega : a ≤ a) (by omega)).trans (hA a (by omega)).2
  have hhi₂ : profileMinimum A (a + 10 * q) b ≤ 1 :=
    (profileMinimum_le (by omega : a + 10 * q ≤ a + 10 * q) hmargin).trans
      (hA (a + 10 * q) (hmargin.trans hb)).2
  unfold profileBudget
  constructor <;> linarith

end FalconerThetaGauge
