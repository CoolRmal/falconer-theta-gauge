/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Tactic.Linarith

/-!
# Summable reconstruction

This file proves the Banach-space convergence step in Lemma 4.2 of the source manuscript.
The good frequency pieces need a square-sum bound, rather than summable individual norms.
The discarded pieces are summable in the first norm. Continuous additive maps into a common
Hausdorff topological group identify the resulting two sums with the reconstructed source.

The concrete Fourier multiplier estimates and identification with a measure are separate
analytic obligations; this file does not claim the full measure-theoretic criterion.
-/

@[expose] public section

noncomputable section

open Filter
open MeasureTheory
open scoped Topology ENNReal Classical

namespace FalconerThetaGauge

/-- The dyadic frequency shell used in Lemma 4.2, with integer exponents so scale zero
also has lower endpoint one half. -/
def dyadicFrequencyShell (N : ℕ) : Set ℝ :=
  {r | (2 : ℝ) ^ ((N : ℤ) - 1) ≤ |r| ∧ |r| ≤ (2 : ℝ) ^ ((N : ℤ) + 1)}

/-- At each frequency, at most three dyadic shells in any finite list overlap. -/
theorem card_dyadicFrequencyShell_indices_le (s : Finset ℕ) (r : ℝ) :
    (s.filter fun N ↦ r ∈ dyadicFrequencyShell N).card ≤ 3 := by
  classical
  let t := s.filter fun N ↦ r ∈ dyadicFrequencyShell N
  change t.card ≤ 3
  by_cases ht : t.Nonempty
  · let k := t.min' ht
    have hk : r ∈ dyadicFrequencyShell k := (Finset.mem_filter.mp (t.min'_mem ht)).2
    have hsub : t ⊆ Finset.Icc k (k + 2) := by
      intro n hn
      have hnShell : r ∈ dyadicFrequencyShell n := (Finset.mem_filter.mp hn).2
      have hpow : (2 : ℝ) ^ ((n : ℤ) - 1) ≤ (2 : ℝ) ^ ((k : ℤ) + 1) :=
        hnShell.1.trans hk.2
      have hupper : (n : ℤ) - 1 ≤ (k : ℤ) + 1 :=
        (zpow_le_zpow_iff_right₀ (show 1 < (2 : ℝ) from one_lt_two)).mp hpow
      have hlower : k ≤ n := Finset.min'_le t n hn
      exact Finset.mem_Icc.mpr ⟨hlower, by omega⟩
    calc
      t.card ≤ (Finset.Icc k (k + 2)).card := Finset.card_le_card hsub
      _ = 3 := by rw [Nat.card_Icc]; omega
  · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp only [hempty, Finset.card_empty, Nat.zero_le]

/-- A sum with at most `K` nonzero terms obeys the finite-overlap square bound. -/
theorem norm_sum_sq_le_of_card_nonzero_le
    {ι E : Type*} [NormedAddCommGroup E] (s : Finset ι) (f : ι → E) (K : ℕ)
    (hcard : (s.filter fun n ↦ f n ≠ 0).card ≤ K) :
    ‖∑ n ∈ s, f n‖ ^ 2 ≤ (K : ℝ) * ∑ n ∈ s, ‖f n‖ ^ 2 := by
  classical
  let t := s.filter fun n ↦ f n ≠ 0
  have hsum : (∑ n ∈ s, f n) = ∑ n ∈ t, f n := (Finset.sum_filter_ne_zero s).symm
  have hsq : (∑ n ∈ t, ‖f n‖ ^ 2) = ∑ n ∈ s, ‖f n‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnt
    have hzero : f n = 0 := by simpa [t, hn] using hnt
    simp [hzero]
  calc
    _ = ‖∑ n ∈ t, f n‖ ^ 2 := by rw [hsum]
    _ ≤ (∑ n ∈ t, ‖f n‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).mpr
        (norm_sum_le t f)
    _ ≤ (t.card : ℝ) * ∑ n ∈ t, ‖f n‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (K : ℝ) * ∑ n ∈ t, ‖f n‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    _ = _ := by rw [hsq]

/-- The second-norm square of an actual `L²` function is its squared-norm integral. -/
theorem l2_norm_sq_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- Bounded overlap of the supports gives a quadratic bound for finite sums in `L²`. -/
theorem l2_finite_sum_square_bound_of_overlap
    {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (good : ι → Lp E 2 μ) (K : ℕ)
    (hoverlap : ∀ s : Finset ι,
      ∀ᵐ x ∂μ, (s.filter fun n ↦ good n x ≠ 0).card ≤ K)
    (s : Finset ι) :
    ‖∑ n ∈ s, good n‖ ^ 2 ≤ (K : ℝ) * ∑ n ∈ s, ‖good n‖ ^ 2 := by
  classical
  have hsquare (f : Lp E 2 μ) : Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  calc
    _ = ∫ x, ‖(∑ n ∈ s, good n) x‖ ^ 2 ∂μ := l2_norm_sq_eq_integral_norm_sq _
    _ ≤ ∫ x, (K : ℝ) * ∑ n ∈ s, ‖good n x‖ ^ 2 ∂μ := by
      apply integral_mono_ae (hsquare _) ((integrable_finsetSum s
        (fun n _ ↦ hsquare (good n))).const_mul (K : ℝ))
      filter_upwards [Lp.coeFn_finsetSum s good, hoverlap s] with x hx hcard
      simpa only [hx, Finset.sum_apply] using
        norm_sum_sq_le_of_card_nonzero_le s (fun n ↦ good n x) K hcard
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum s (fun n _ ↦ hsquare (good n))]
      simp_rw [← l2_norm_sq_eq_integral_norm_sq]

/-- A uniform quadratic bound on finite sums and summable scalar energies imply convergence
of the vector series. This includes the finite-overlap bound for the good frequency pieces. -/
theorem summable_of_finite_square_sum_bound
    {ι F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {good : ι → F} {energy : ι → ℝ} {C : ℝ}
    (hC : 0 < C) (henergy : Summable energy)
    (hbound : ∀ s : Finset ι, ‖∑ n ∈ s, good n‖ ^ 2 ≤ C * ∑ n ∈ s, energy n) :
    Summable good := by
  refine summable_iff_vanishing_norm.2 fun ε hε ↦ ?_
  have hδ : 0 < ε ^ 2 / C := div_pos (sq_pos_of_pos hε) hC
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 henergy _ hδ
  refine ⟨s, fun t hts ↦ ?_⟩
  have htail : (∑ n ∈ t, energy n) * C < ε ^ 2 :=
    (lt_div_iff₀ hC).mp ((le_abs_self _).trans_lt (hs t hts))
  have hnorm := norm_nonneg (∑ n ∈ t, good n)
  have hquad := hbound t
  nlinarith

/-- Square-summable `L²` pieces with uniformly bounded support overlap form a convergent
`L²` series. Dyadic Fourier annuli are the intended application, with overlap constant three. -/
theorem summable_l2_of_finite_overlap
    {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (good : ι → Lp E 2 μ) {K : ℕ} (hK : 0 < K)
    (henergy : Summable (fun n ↦ ‖good n‖ ^ 2))
    (hoverlap : ∀ s : Finset ι,
      ∀ᵐ x ∂μ, (s.filter fun n ↦ good n x ≠ 0).card ≤ K) :
    Summable good :=
  summable_of_finite_square_sum_bound (Nat.cast_pos.mpr hK) henergy
    (l2_finite_sum_square_bound_of_overlap good K hoverlap)

/-- Actual `L²` functions supported in the manuscript's dyadic shells form a convergent
`L²` series as soon as their squared second norms are summable. -/
theorem summable_l2_of_dyadicFrequencyShell_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (good : ℕ → Lp E 2 (volume : Measure ℝ))
    (henergy : Summable (fun n ↦ ‖good n‖ ^ 2))
    (hsupport : ∀ n, ∀ᵐ r ∂(volume : Measure ℝ),
      good n r ≠ 0 → r ∈ dyadicFrequencyShell n) :
    Summable good := by
  apply summable_l2_of_finite_overlap good (show 0 < 3 by decide) henergy
  intro s
  filter_upwards [ae_all_iff.mpr hsupport] with r hr
  have hsub : (s.filter fun n ↦ good n r ≠ 0) ⊆
      s.filter fun n ↦ r ∈ dyadicFrequencyShell n := by
    intro n hn
    obtain ⟨hns, hnzero⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hns, hr n hnzero⟩
  exact (Finset.card_le_card hsub).trans (card_dyadicFrequencyShell_indices_le s r)

/-- An approximation reconstructed from summable first-norm errors and square-controlled
good pieces has a limit represented by the sum of the two Banach-space limits. -/
theorem reconstruction_of_summable_errors_and_square_bound
    {E F G : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [CompleteSpace F]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    (embedError : ContinuousAddMonoidHom E G) (embedGood : ContinuousAddMonoidHom F G)
    (base : E) {error : ℕ → E} {good : ℕ → F} {energy : ℕ → ℝ} {C : ℝ}
    {approx : ℕ → G} {source : G}
    (herror : Summable (fun n ↦ ‖error n‖)) (hC : 0 < C)
    (henergy : Summable energy)
    (hbound : ∀ s : Finset ℕ, ‖∑ n ∈ s, good n‖ ^ 2 ≤ C * ∑ n ∈ s, energy n)
    (happrox : ∀ N, approx N = embedError (base + ∑ n ∈ Finset.range N, error n) +
      embedGood (∑ n ∈ Finset.range N, good n))
    (hsource : Tendsto approx atTop (𝓝 source)) :
    ∃ first : E, ∃ second : F,
      HasSum error (first - base) ∧ HasSum good second ∧
      source = embedError first + embedGood second := by
  have he : Summable error := herror.of_norm
  have hg : Summable good := summable_of_finite_square_sum_bound hC henergy hbound
  refine ⟨base + ∑' n, error n, ∑' n, good n, ?_, hg.hasSum, ?_⟩
  · simpa only [add_sub_cancel_left] using he.hasSum
  · apply tendsto_nhds_unique hsource
    rw [show approx = fun N ↦ embedError (base + ∑ n ∈ Finset.range N, error n) +
      embedGood (∑ n ∈ Finset.range N, good n) from funext happrox]
    exact (embedError.continuous.tendsto _).comp
      (tendsto_const_nhds.add he.hasSum.tendsto_sum_nat) |>.add
        ((embedGood.continuous.tendsto _).comp hg.hasSum.tendsto_sum_nat)

end FalconerThetaGauge
