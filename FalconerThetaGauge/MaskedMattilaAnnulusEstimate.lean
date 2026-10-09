/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaNormalizedEstimate

/-! # The literal full annulus in source Estimate 7.5 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Metric

namespace FalconerThetaGauge

theorem scalarFourierAnnulusIntegral_eq_twice_window (η : Measure ℝ)
    [IsFiniteMeasure η] (v : ℕ) :
    scalarFourierAnnulusIntegral η ((v : ℝ) - 1) ((v : ℝ) + 1) =
      2 * ∫ r in bilinearFrequencyWindow v, ‖angularScalarFourier η r‖ ^ 2 := by
  let f := fun r ↦ ‖angularScalarFourier η r‖ ^ 2
  let A := (2 : ℝ) ^ v / 2
  let B := 2 * (2 : ℝ) ^ v
  have hA : 0 < A := by positivity
  have hAB : A ≤ B := by dsimp [A, B]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) v]
  have hf : Continuous f := (continuous_angularScalarFourier η).norm.pow 2
  have hI : IntegrableOn f (Icc A B) := hf.integrableOn_Icc
  have hJ : IntegrableOn f (Icc (-B) (-A)) := hf.integrableOn_Icc
  have hdis : Disjoint (Ioc A B) (Ico (-B) (-A)) := by
    apply Set.disjoint_left.mpr
    intro r hr hs
    linarith [hr.1, hs.2]
  have hs : scalarFourierAnnulus ((v : ℝ) - 1) ((v : ℝ) + 1) =
      Ioc A B ∪ Ico (-B) (-A) := by
    ext r
    simp only [scalarFourierAnnulus, mem_ofPred_eq,
      Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, Real.rpow_one,
      mul_comm ((2 : ℝ) ^ v) 2, mem_union, mem_Ioc, mem_Ico]
    change (A < |r| ∧ |r| ≤ B) ↔ (A < r ∧ r ≤ B) ∨ (-B ≤ r ∧ r < -A)
    by_cases hr : 0 ≤ r
    · rw [abs_of_nonneg hr]
      constructor
      · exact fun h ↦ Or.inl h
      · rintro (h | h)
        · exact h
        · exfalso; linarith [h.2]
    · rw [abs_of_neg (lt_of_not_ge hr)]
      constructor
      · intro h; right; constructor <;> linarith [h.1, h.2]
      · rintro (h | h)
        · exfalso; linarith [h.1]
        · constructor <;> linarith [h.1, h.2]
  have heven : (fun r ↦ f (-r)) = f := by
    funext r
    exact congrArg (fun x : ℝ ↦ x ^ 2) (norm_angularScalarFourier_neg η r)
  have hneg : (∫ r in Icc (-B) (-A), f r) = ∫ r in Icc A B, f r := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -B ≤ -A),
      ← intervalIntegral.integral_of_le hAB]
    have he := intervalIntegral.integral_comp_neg f (a := A) (b := B)
    rw [heven] at he
    exact he.symm
  unfold scalarFourierAnnulusIntegral
  rw [hs, setIntegral_union hdis measurableSet_Ico
    (hI.mono_set Ioc_subset_Icc_self) (hJ.mono_set Ico_subset_Icc_self),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ico, hneg]
  dsimp [bilinearFrequencyWindow, A, B, f]
  ring

set_option maxHeartbeats 800000 in
theorem builtMaskedDistance_mattila_annulus_estimate {θ : ℝ} {N : ℕ}
    (hpar : ParameterFacts θ N)
    (ρ₁ ρ₂ : Measure Plane) [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    {X Y : Set Plane} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hm : 0 < ρ₁.real X * ρ₂.real Y)
    (hXball : X ⊆ closedBall x₀ ρ) (hYball : Y ⊆ closedBall y₀ ρ)
    (width α a : ℝ) (I₁ I₂ : Finset ProfileScheduleTest) {L₁ L₂ : ℕ}
    (hL₁ : ∀ test ∈ I₁, test.length ≤ L₁)
    (hL₂ : ∀ test ∈ I₂, test.length ≤ L₂)
    (hc₁ : I₁.card ≤ N ^ 2 + 1) (hc₂ : I₂.card ≤ N ^ 2 + 1)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) (cutoffK v : ℕ) (hv : v ≤ N)
    (hC : Real.sqrt 2 / dist x₀ y₀ ≤ 6 * (2 : ℝ) ^ a)
    (hdir : ∀ x ∈ X, ∀ y ∈ Y, pairDirection x y ∈ closedDirectionArc α (1 / 40))
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - a)
    (hlength₁ : 2 * (L₁ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hlength₂ : 2 * (L₂ : ℝ) ≤ (v : ℝ) - a + tolerance θ N * N)
    (hΛ : ∀ r ∈ bilinearFrequencyWindow v, ∀ x ∈ X, ∀ y ∈ Y,
      (2 : ℝ) ^ ((v : ℝ) - a - 4) ≤ r * dist x y)
    (hterminal : ∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ dist x y) :
    scalarFourierAnnulusIntegral
        (builtMaskedDistanceMeasure ρ₁ ρ₂ X Y (tolerance θ N * N) width
          (8 * expansionCount θ N) I₁ I₂) ((v : ℝ) - 1) ((v : ℝ) + 1) /
        (ρ₁.real X * ρ₂.real Y) ≤
      2 * scheduledFourierEnergySup ρ₁ ρ₂ X Y (tolerance θ N * N) width
        (8 * expansionCount θ N) I₁ I₂ (2 * expansionCount θ N) cutoffK v +
      (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  let E := tolerance θ N * N
  let T := expansionCount θ N
  let β := builtMaskedDistanceMeasure ρ₁ ρ₂ X Y E width (8 * T) I₁ I₂
  let m := ρ₁.real X * ρ₂.real Y
  let F := scheduledFourierEnergySup ρ₁ ρ₂ X Y E width (8 * T) I₁ I₂ (2 * T) cutoffK v
  let : IsFiniteMeasure β := isFiniteMeasure_builtMaskedDistanceMeasure ρ₁ ρ₂ hX hY
    (by positivity : 0 < (2 : ℝ) ^ (-(N : ℝ) - 4)) hterminal E width (8 * T) I₁ I₂
  have hF : 0 ≤ F := scheduledFourierEnergySup_nonneg ρ₁ ρ₂ X Y E width
    (8 * T) I₁ I₂ (by omega) cutoffK v
  have hπ : 121 / (25 * Real.pi) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hi := integral_builtMaskedDistance_window_le hpar ρ₁ ρ₂ hρ hsep hX hY
    hXball hYball width α a I₁ I₂ hL₁ hL₂ hc₁ hc₂ hL₁N hL₂N cutoffK v hC
    hdir hw hlength₁ hlength₂ hΛ hterminal
  have hbase : scalarFourierAnnulusIntegral β ((v : ℝ) - 1) ((v : ℝ) + 1) ≤
      2 * m * F + (2 : ℝ) ^ (-(390 * (N : ℝ))) * m ^ 2 := by
    calc
      _ = 2 * ∫ r in bilinearFrequencyWindow v, ‖angularScalarFourier β r‖ ^ 2 :=
        scalarFourierAnnulusIntegral_eq_twice_window β v
      _ ≤ 2 * (121 / (50 * Real.pi) * m * F +
          3 * (2 : ℝ) ^ v * ((2 : ℝ) ^ (-(200 * (N : ℝ)))) ^ 2 * m ^ 2) :=
        mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = 121 / (25 * Real.pi) * m * F +
          (6 * (2 : ℝ) ^ v * ((2 : ℝ) ^ (-(200 * (N : ℝ)))) ^ 2) * m ^ 2 := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hπ (by positivity)) hF)
        (mul_le_mul_of_nonneg_right
          (mattila_shell_error_budget (by have := hpar.1; omega) hv) (sq_nonneg _))
  have hm₁ : m ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul measureReal_le_one measureReal_le_one
        (by positivity) (by norm_num)
      _ = _ := one_mul _
  apply (div_le_iff₀ hm).mpr
  apply hbase.trans
  calc
    _ ≤ 2 * m * F + (2 : ℝ) ^ (-(390 * (N : ℝ))) * m := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = _ := by ring

end FalconerThetaGauge
