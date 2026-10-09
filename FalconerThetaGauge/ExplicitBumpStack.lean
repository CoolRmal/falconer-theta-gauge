module

public import FalconerThetaGauge.ExplicitBumpProbability
public import FalconerThetaGauge.ExplicitBumpWidths
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Finite stacks of genuine box convolutions

Each derivative may be assigned to the next box, leaving a probability density
behind it. The resulting first-norm estimate depends only on the differentiated
widths, not on the arbitrary smooth tail or the total number of boxes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

theorem hasCompactSupport_boxAverage {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (boxAverage a f) := by
  obtain ⟨R, _, hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-(R + a)) (R + a)))
  intro x hx
  rw [mem_Icc, ← abs_le]
  by_contra h
  apply mem_support.mp hx
  apply boxAverage_eq_zero_of_abs_gt ha _ (lt_of_not_ge h)
  intro y hy
  by_contra hfy
  have hbound := hR y (subset_tsupport _ (mem_support.mpr hfy))
  simpa only [Real.norm_eq_abs] using (not_lt_of_ge hbound) hy

def explicitBoxStack (j : ℕ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | K + 1, f => boxAverage (explicitBoxWidth j) (explicitBoxStack (j + 1) K f)

theorem contDiff_explicitBoxStack (j K : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (explicitBoxStack j K f) := by
  induction K generalizing j with
  | zero => exact hf
  | succ K ih => exact contDiff_boxAverage _ (ih (j + 1))

theorem hasCompactSupport_explicitBoxStack (j K : ℕ) {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (explicitBoxStack j K f) := by
  induction K generalizing j with
  | zero => exact hf
  | succ K ih => exact hasCompactSupport_boxAverage (explicitBoxWidth_pos j) (ih (j + 1))

theorem explicitBoxStack_nonneg (j K : ℕ) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ explicitBoxStack j K f x := by
  induction K generalizing j with
  | zero => exact hf
  | succ K ih => exact boxAverage_nonneg (explicitBoxWidth_pos j) (ih (j + 1))

theorem explicitBoxStack_even (j K : ℕ) {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) :
    ∀ x, explicitBoxStack j K f (-x) = explicitBoxStack j K f x := by
  induction K generalizing j with
  | zero => exact hf
  | succ K ih => exact boxAverage_even (ih (j + 1))

theorem integral_explicitBoxStack (j K : ℕ) {f : ℝ → ℝ} (hf : Integrable f volume) :
    (∫ x : ℝ, explicitBoxStack j K f x) = ∫ x : ℝ, f x := by
  have hi (j K : ℕ) : Integrable (explicitBoxStack j K f) volume := by
    induction K generalizing j with
    | zero => exact hf
    | succ K ih => exact integrable_boxAverage (explicitBoxWidth_pos j) (ih (j + 1))
  induction K generalizing j with
  | zero => rfl
  | succ K ih => exact (integral_boxAverage (explicitBoxWidth_pos j) (hi (j + 1) K)).trans (ih (j + 1))

theorem iteratedDeriv_boxDifference (n : ℕ) (a : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (boxDifference a f) = boxDifference a (iteratedDeriv n f) := by
  have hr : ContDiff ℝ n (fun x : ℝ ↦ f (x + a)) := (hf.comp (contDiff_id.add contDiff_const)).of_le (by simp)
  have hl : ContDiff ℝ n (fun x : ℝ ↦ f (x - a)) := (hf.comp (contDiff_id.sub contDiff_const)).of_le (by simp)
  funext x
  change iteratedDeriv n (fun x : ℝ ↦ (2 * a)⁻¹ * (f (x + a) - f (x - a))) x = _
  rw [iteratedDeriv_const_mul _ (hr.sub hl).contDiffAt]
  have hsub : iteratedDeriv n (fun x : ℝ ↦ f (x + a) - f (x - a)) x =
      iteratedDeriv n (fun x : ℝ ↦ f (x + a)) x -
        iteratedDeriv n (fun x : ℝ ↦ f (x - a)) x := by
    have heq : (fun x : ℝ ↦ f (x + a) - f (x - a)) =
        ((fun x : ℝ ↦ f (x + a)) - (fun x : ℝ ↦ f (x - a))) := by
      funext x
      rfl
    rw [heq]
    exact iteratedDeriv_sub hr.contDiffAt hl.contDiffAt
  rw [hsub, iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const]
  rfl

theorem hasCompactSupport_iteratedDeriv (n : ℕ) {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem integrable_iteratedDeriv_of_smooth_compact (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hk : HasCompactSupport f) :
    Integrable (iteratedDeriv n f) volume :=
  (hf.continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv n hk)

theorem iteratedDeriv_explicitBoxStack_succ (j K k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv (k + 1) (explicitBoxStack j (K + 1) f) =
      boxDifference (explicitBoxWidth j) (iteratedDeriv k (explicitBoxStack (j + 1) K f)) := by
  rw [iteratedDeriv_succ']
  change iteratedDeriv k (deriv (boxAverage (explicitBoxWidth j)
    (explicitBoxStack (j + 1) K f))) = _
  rw [deriv_boxAverage _ (contDiff_explicitBoxStack _ _ hf).continuous]
  exact iteratedDeriv_boxDifference k _ (contDiff_explicitBoxStack _ _ hf)

/-- The first `k` derivatives cost only the first `k` box half-widths, even if
the full smoothing stack has arbitrarily many further boxes. -/
theorem integral_norm_iteratedDeriv_explicitBoxStack_le
    (j K k : ℕ) (hk : k ≤ K) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport f) (hpos : ∀ x, 0 ≤ f x) (hmass : (∫ x : ℝ, f x) = 1) :
    (∫ x : ℝ, ‖iteratedDeriv k (explicitBoxStack j K f) x‖) ≤
      ∏ i ∈ Finset.range k, (explicitBoxWidth (j + i))⁻¹ := by
  have hzero (j K : ℕ) : (∫ x : ℝ, ‖iteratedDeriv 0 (explicitBoxStack j K f) x‖) = 1 := by
    simp_rw [iteratedDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg (explicitBoxStack_nonneg j K hpos _)]
    exact (integral_explicitBoxStack j K
      (hf.continuous.integrable_of_hasCompactSupport hcompact)).trans hmass
  induction K generalizing j k with
  | zero =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp only [hzero, Finset.range_zero, Finset.prod_empty, le_refl]
  | succ K ih =>
    cases k with
    | zero => simp only [hzero, Finset.range_zero, Finset.prod_empty, le_refl]
    | succ k =>
      have hk' : k ≤ K := Nat.le_of_succ_le_succ hk
      rw [iteratedDeriv_explicitBoxStack_succ j K k hf]
      calc
        _ ≤ (explicitBoxWidth j)⁻¹ * ∫ x : ℝ,
            ‖iteratedDeriv k (explicitBoxStack (j + 1) K f) x‖ :=
          integral_norm_boxDifference_le (explicitBoxWidth_pos j)
            (integrable_iteratedDeriv_of_smooth_compact k
              (contDiff_explicitBoxStack _ _ hf) (hasCompactSupport_explicitBoxStack _ _ hcompact))
        _ ≤ (explicitBoxWidth j)⁻¹ *
            ∏ i ∈ Finset.range k, (explicitBoxWidth (j + 1 + i))⁻¹ :=
          mul_le_mul_of_nonneg_left (ih (j + 1) k hk') (inv_nonneg.mpr (explicitBoxWidth_pos j).le)
        _ = _ := by
          rw [Finset.prod_range_succ']
          simp only [Nat.add_zero]
          have hp : (∏ i ∈ Finset.range k, (explicitBoxWidth (j + 1 + i))⁻¹) =
              ∏ i ∈ Finset.range k, (explicitBoxWidth (j + (i + 1)))⁻¹ := by
            apply Finset.prod_congr rfl
            intro i hi
            congr 2
            omega
          rw [hp, mul_comm]

end FalconerThetaGauge
