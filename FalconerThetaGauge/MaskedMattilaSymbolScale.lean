module

public import FalconerThetaGauge.MaskedMattilaSymbolRegularity

/-! # Actual scheduled-symbol scales satisfy the Step 0 inversion budgets -/

@[expose] public section

noncomputable section

namespace FalconerThetaGauge

def builtPairSymbolScale (T : ℕ) (E : ℝ) (I₁ I₂ : Finset ProfileScheduleTest)
    (L₁ L₂ : ℕ) : ℝ :=
  max 1 (scheduledSymbolScale T E I₁ L₁) + max 1 (scheduledSymbolScale T E I₂ L₂)

theorem scheduledSymbolScale_max_one_le {T : ℕ} (hT : 1 ≤ T) (N : ℕ)
    (E : ℝ) (I : Finset ProfileScheduleTest) (L : ℕ) (hcard : I.card ≤ N ^ 2 + 1)
    {F : ℝ} (hF : 1 ≤ F)
    (hfactor : max 1 ((2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-E)) ≤ F) :
    max 1 (scheduledSymbolScale T E I L) ≤
      128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * F := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hcard' : (I.card : ℝ) ≤ (N : ℝ) ^ 2 + 1 := by exact_mod_cast hcard
  have hpoly : 1 ≤ 128 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) := by
    have ht : 1 ≤ (T : ℝ) ^ 2 := by nlinarith
    have hn : 1 ≤ (N : ℝ) ^ 2 + 1 := by nlinarith [sq_nonneg (N : ℝ)]
    nlinarith
  apply max_le
  · have h := mul_le_mul hpoly hF (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa only [one_mul] using h
  · unfold scheduledSymbolScale
    gcongr

theorem builtPairSymbolScale_le_frequency {T : ℕ} (hT : 1 ≤ T) (N : ℕ)
    {E w : ℝ} (hE : 0 ≤ E) (hw : 10 * E ≤ w)
    (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁ : 2 * (L₁ : ℝ) ≤ w + E) (hL₂ : 2 * (L₂ : ℝ) ≤ w + E) :
    builtPairSymbolScale T E I₁ I₂ L₁ L₂ ≤
      256 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ (w / 2 - E / 2) := by
  have hF : 1 ≤ (2 : ℝ) ^ (w / 2 - E / 2) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have h₁ := scheduledSymbolScale_max_one_le hT N E I₁ L₁ hc₁ hF
    (scheduled_mask_frequency_factor_le hE hw hL₁)
  have h₂ := scheduledSymbolScale_max_one_le hT N E I₂ L₂ hc₂ hF
    (scheduled_mask_frequency_factor_le hE hw hL₂)
  unfold builtPairSymbolScale
  linarith

theorem builtPairSymbolScale_le_terminal {T N : ℕ} (hT : 1 ≤ T) {E : ℝ}
    (hE : E ≤ N) (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁ : L₁ ≤ N) (hL₂ : L₂ ≤ N) :
    builtPairSymbolScale T E I₁ I₂ L₁ L₂ ≤
      256 * (T : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ ((N : ℝ) - E) := by
  have hF : 1 ≤ (2 : ℝ) ^ ((N : ℝ) - E) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have h₁ := scheduledSymbolScale_max_one_le hT N E I₁ L₁ hc₁ hF
    (scheduled_mask_terminal_factor_le hE hL₁)
  have h₂ := scheduledSymbolScale_max_one_le hT N E I₂ L₂ hc₂ hF
    (scheduled_mask_terminal_factor_le hE hL₂)
  unfold builtPairSymbolScale
  linarith

end FalconerThetaGauge
