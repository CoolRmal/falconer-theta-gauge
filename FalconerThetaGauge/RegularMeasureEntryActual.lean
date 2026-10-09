/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntry

/-!
# The entry properties of actual retained regular pieces

The exact parameter facts, actual gauge lower barrier and largest-cell excess
give all three conclusions of Lemma 9.2, including the long interval and its
post-entry budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem gaugeExcess_le_of_le {θ : ℝ} (hθ : 0 ≤ θ) {N : ℕ} (hN : 0 < N)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : gaugeExcess θ N a ≤ gaugeExcess θ N b := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow (mul_nonneg ha hlog.le) (mul_le_mul_of_nonneg_right hab hlog.le) hθ)
    (mul_pos hN' hlog).le

/-- The actual entry depth for the heaviest-cell excess of one probability. -/
def regularMeasureEntryDepth (ρ : Measure Plane) (θ : ℝ) (N : ℕ) : ℕ :=
  profileEntryDepth (regularMeasureExcess ρ N) (gain θ N) N

/-- Lemma 9.2 for every actual kept part, including its post-entry budget. -/
theorem regularDyadicPart_entry_properties (μ : Measure Plane) [IsProbabilityMeasure μ]
    {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hball : HasGaugeBallBound μ θ C)
    {N : ℕ} (hpar : ParameterFacts θ N)
    (hconstant : Real.log C / Real.log 2 ≤ blockParameter θ N * N / 2)
    {t : List ℕ} (ht : t ∈ regularDyadicKeptTypes μ (tolerance θ N) (blockParameter θ N) N) :
    let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t
    let A := regularMeasureExcess ρ N
    let c := regularMeasureEntryDepth ρ θ N
    ⌊gain θ N * N⌋₊ ≤ c ∧
      (c : ℝ) < (N : ℝ) / 4 ∧
      100 * blockCount θ N < N - c ∧
      (∀ n : ℕ, c ≤ n → n ≤ N → gain θ N - 1 / (N : ℝ) < A n) ∧
      2 * gain θ N - 2 / (N : ℝ) ≤ profileBudget A (blockCount θ N) c N ∧
      profileHeight A c 0 c ≤ gain θ N + blockParameter θ N := by
  let ρ := regularDyadicPartMeasure μ (tolerance θ N) N t
  let A := regularMeasureExcess ρ N
  let β := gain θ N
  let κ := blockParameter θ N
  let c := profileEntryDepth A β N
  rcases hpar with ⟨hN₄, _, _, _, hP4⟩
  rcases hP4 with ⟨_, hκβ, hβsmall, _, _, _, _, _⟩
  have hN : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ : 0 < β := gain_pos θ hN
  have hκ : 0 < κ := blockParameter_pos θ hN
  have hβ₁ : β ≤ 1 := by dsimp [β]; linarith
  have hκβ' : κ < β := by dsimp [κ, β]; linarith
  have hκsmall : κ ≤ 1 / 10000 := hκβ.trans hβsmall
  obtain ⟨hA0, hAlip, hAlower, hAupper⟩ :=
    regularDyadicPartMeasure_excess_properties μ hθ hC hκ.le hball hN hconstant ht
  have hzero : A 0 ≤ β := by rw [show A 0 = 0 from hA0]; exact hβ.le
  have hfloor : ⌊β * N⌋₊ ≤ c := floor_gain_mul_le_profileEntryDepth hN hβ.le hβ₁
    (fun n _ ↦ hAupper n)
  have hcquarter : (c : ℝ) < (N : ℝ) / 4 := by
    apply profileEntryDepth_lt_quarter hzero
    intro n _ hn
    have hmono := gaugeExcess_le_of_le hθ.le hN (by positivity : 0 ≤ (N : ℝ) / 4) hn
    have hgain : gaugeExcess θ N ((N : ℝ) / 4) = 2 * β := by dsimp [β, gain]; ring
    rw [hgain] at hmono
    have hlo := hAlower n
    dsimp [A, κ, β] at *
    linarith
  have hcN : c < N := by
    have hreal : (c : ℝ) < N := by linarith
    exact_mod_cast hreal
  have hlong : 100 * blockCount θ N < N - c := by
    have hκscale : κ * N = (blockCount θ N : ℝ) := blockParameter_mul_scale θ hN
    have hκN := mul_le_mul_of_nonneg_right hκsmall hN'.le
    have hreal : ((100 * blockCount θ N : ℕ) : ℝ) < (N - c : ℕ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hcN.le]
      nlinarith
    exact_mod_cast hreal
  have hstep : ∀ n < N, |A (n + 1) - A n| ≤ 1 / (N : ℝ) := by
    intro n _
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, abs_one] using hAlip (n + 1) n
  have hintervallower : ∀ n : ℕ, c ≤ n → n ≤ N → β - 1 / (N : ℝ) < A n :=
    fun _ hnc hnN ↦ profileEntryDepth_interval_lower hN hcN hstep hnc hnN
  have hbudget : 2 * β - 2 / (N : ℝ) ≤ profileBudget A (blockCount θ N) c N :=
    profileEntryDepth_budget_lower hN (by omega) hcN hstep
  have hcost : profileHeight A c 0 c ≤ β + κ := by
    apply profileEntryDepth_height_le hzero
    intro n _
    have hlo := hAlower n
    have hg := gaugeExcess_nonneg θ hN n
    dsimp [A, κ]
    linarith
  exact ⟨hfloor, hcquarter, hlong, hintervallower, hbudget, hcost⟩

end FalconerThetaGauge
