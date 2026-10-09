/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.GaugeFrostmanMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Weak compactness for the finite Frostman measures

Adapted from `FalconerPacking.WeakLimit` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/WeakLimit.lean

Probability measures carried by one compact planar set form a compact set for the weak topology.
Consequently every sequence of the normalized atomic Frostman measures has a weakly convergent
subsequence whose limit is still carried by the same compact set.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace FalconerThetaGauge.GaugeFrostman

/-- Probability measures that give no mass to the complement of `K`. -/
def probabilityMeasuresSupportedOn (K : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) :=
  {μ | (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0}

/-- Probability measures carried by a compact planar set form a compact set in the weak
topology. -/
theorem isCompact_probabilityMeasuresSupportedOn {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) : IsCompact (probabilityMeasuresSupportedOn K) := by
  have hcompact :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
      (E := EuclideanSpace ℝ (Fin 2)) (u := fun _ ↦ 0) (K := fun _ ↦ K)
      tendsto_const_nhds (fun _ ↦ hK) (Or.inl inferInstance)
  have heq : probabilityMeasuresSupportedOn K =
      {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) | ∀ n : ℕ, μ Kᶜ ≤ 0} := by
    ext μ
    simp only [probabilityMeasuresSupportedOn, mem_ofPred_eq, nonpos_iff_eq_zero]
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simp
  rw [heq]
  exact hcompact

/-- Every sequence of probability measures carried by one compact set has a weakly convergent
subsequence, and its limit remains carried by that set. -/
theorem exists_tendsto_subseq_of_supported {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (hμ : ∀ n, μ n ∈ probabilityMeasuresSupportedOn K) :
    ∃ ν ∈ probabilityMeasuresSupportedOn K, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨ν, hν, φ, hφ, hconv⟩ :=
    (isCompact_probabilityMeasuresSupportedOn hK).isSeqCompact hμ
  exact ⟨ν, hν, φ, hφ, hconv⟩

/-- A normalized atomic Frostman measure whose selected atoms lie in `K` belongs to the compact
space of probability measures carried by `K`. -/
theorem weightProbabilityMeasure_mem_probabilityMeasuresSupportedOn
    {S : Finset (Fin 2 → ℤ)}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K)
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k ∈ S, pt k ∈ K) :
    weightProbabilityMeasure S pt w ∈ probabilityMeasuresSupportedOn K :=
  weightProbabilityMeasure_compl_eq_zero hK hw hmass hpt

/-- Choose one normalized finite Frostman approximation at every positive depth.  The ball
constant is uniform, and the `n`-th approximation has the estimate through depth `n + 1`. -/
theorem exists_probabilityMeasure_approximation_sequence
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) (hcontent : 0 < gaugeContent θ K) :
    ∃ μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      (∀ n, μ n ∈ probabilityMeasuresSupportedOn K) ∧
      ∀ n i, i ≤ n + 1 → ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ K)⁻¹) *
            (4 * ENNReal.ofReal (realGauge θ (dyadicRadius i))) := by
  have hex : ∀ n : ℕ, ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0 ∧
      ∀ i ≤ n + 1, ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ K)⁻¹) *
            (4 * ENNReal.ofReal (realGauge θ (dyadicRadius i))) := by
    intro n
    exact exists_compact_probabilityMeasure_all_scale_estimates hK hθ₀ hθ₁ hcontent
      (Nat.succ_le_succ (Nat.zero_le n))
  choose μ hsupp hbound using hex
  refine ⟨μ, ?_, ?_⟩
  · exact fun n ↦ hsupp n
  · exact fun n i hi ↦ hbound n i hi

/-- The finite Frostman approximations have a weakly convergent subsequence supported on `K`. -/
theorem exists_tendsto_frostman_approximation_subseq
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) (hcontent : 0 < gaugeContent θ K) :
    ∃ (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
      (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (φ : ℕ → ℕ),
      ν ∈ probabilityMeasuresSupportedOn K ∧ StrictMono φ ∧
      Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      ∀ n i, i ≤ n + 1 → ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ K)⁻¹) *
            (4 * ENNReal.ofReal (realGauge θ (dyadicRadius i))) := by
  obtain ⟨μ, hsupp, hbound⟩ :=
    exists_probabilityMeasure_approximation_sequence hK hθ₀ hθ₁ hcontent
  obtain ⟨ν, hν, φ, hφ, hconv⟩ := exists_tendsto_subseq_of_supported hK μ hsupp
  exact ⟨μ, ν, φ, hν, hφ, hconv, hbound⟩

/-- An eventual uniform upper bound on the mass of an open ball passes to a weak limit. -/
theorem probabilityMeasure_ball_le_of_tendsto_of_eventually_le
    {μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))}
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))}
    (hconv : Tendsto μ atTop (𝓝 ν)) {x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {C : ℝ≥0∞}
    (hbound : ∀ᶠ n in atTop,
      (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤ C) :
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤ C := by
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hconv Metric.isOpen_ball).trans ?_
  calc
    atTop.liminf (fun n ↦
        (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r))
      ≤ atTop.liminf (fun _ : ℕ ↦ C) := Filter.liminf_le_liminf hbound
    _ = C := Filter.liminf_const C

/-- The weak limit of the finite constructions is supported on `K` and retains every dyadic-scale
ball estimate. -/
theorem exists_probabilityMeasure_dyadic_frostman
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) (hcontent : 0 < gaugeContent θ K) :
    ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      ν ∈ probabilityMeasuresSupportedOn K ∧
      ∀ i x r, 0 < r → r ≤ dyadicCoverRadius i →
        (ν : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ K)⁻¹) *
            (4 * ENNReal.ofReal (realGauge θ (dyadicRadius i))) := by
  obtain ⟨μ, ν, φ, hν, hφ, hconv, hbound⟩ :=
    exists_tendsto_frostman_approximation_subseq hK hθ₀ hθ₁ hcontent
  refine ⟨ν, hν, ?_⟩
  intro i x r hr hri
  apply probabilityMeasure_ball_le_of_tendsto_of_eventually_le hconv
  filter_upwards [eventually_ge_atTop i] with k hk
  apply hbound (φ k) i
  · exact hk.trans (hφ.le_apply.trans (Nat.le_add_right (φ k) 1))
  · exact hr
  · exact hri

theorem dyadicRadius_eq_half_pow (i : ℕ) : dyadicRadius i = (1 / 2 : ℝ) ^ i := by
  simp [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast, one_div, inv_pow]

theorem dyadicCoverRadius_eq_dyadicRadius_succ (i : ℕ) :
    dyadicCoverRadius i = dyadicRadius (i + 1) := by
  simp [dyadicCoverRadius, dyadicRadius, Nat.cast_add, Nat.cast_one]

/-- Compare an arbitrary radius with consecutive dyadic side lengths. -/
theorem exists_dyadicRadius_bracket {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ i : ℕ, dyadicRadius (i + 1) < r ∧ r ≤ dyadicRadius i := by
  obtain ⟨i, hi, hi'⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨i, by simpa only [dyadicRadius_eq_half_pow] using hi,
    by simpa only [dyadicRadius_eq_half_pow] using hi'⟩

theorem dyadicRadius_eq_four_mul_add_two (i : ℕ) :
    dyadicRadius i = 4 * dyadicRadius (i + 2) := by
  simp only [dyadicRadius_eq_half_pow, pow_add]
  ring

theorem realGauge_mul_eight_le {θ r : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hr : 0 < r) (hreight : 8 * r ≤ 1) :
    realGauge θ (8 * r) ≤ gaugeDoublingConstant θ ^ 3 * realGauge θ r := by
  have hC : 0 ≤ gaugeDoublingConstant θ := (gaugeDoublingConstant_pos θ).le
  have h4 : realGauge θ (8 * r) ≤ gaugeDoublingConstant θ * realGauge θ (4 * r) := by
    simpa only [show 2 * (4 * r) = 8 * r by ring] using
      realGauge_double_le hθ₀ hθ₁ (by positivity : (0 : ℝ) < 4 * r) (by linarith)
  have h2 : realGauge θ (4 * r) ≤ gaugeDoublingConstant θ * realGauge θ (2 * r) := by
    simpa only [show 2 * (2 * r) = 4 * r by ring] using
      realGauge_double_le hθ₀ hθ₁ (by positivity : (0 : ℝ) < 2 * r) (by linarith)
  calc
    realGauge θ (8 * r) ≤ gaugeDoublingConstant θ * realGauge θ (4 * r) := h4
    _ ≤ gaugeDoublingConstant θ * (gaugeDoublingConstant θ * realGauge θ (2 * r)) :=
      mul_le_mul_of_nonneg_left h2 hC
    _ ≤ gaugeDoublingConstant θ * (gaugeDoublingConstant θ *
        (gaugeDoublingConstant θ * realGauge θ r)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (realGauge_double_le hθ₀ hθ₁ hr (by linarith)) hC) hC
    _ = gaugeDoublingConstant θ ^ 3 * realGauge θ r := by ring

/-- Dyadic estimates imply the gauge Frostman estimate on every closed ball of
positive radius below one. Large radii are covered by the probability bound. -/
theorem closedBall_bound_of_dyadic_ball_bound (μ : ProbabilityMeasure Plane)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hbound : ∀ i x r, 0 < r → r ≤ dyadicCoverRadius i →
      (μ : Measure Plane) (Metric.ball x r) ≤
        A * (4 * ENNReal.ofReal (realGauge θ (dyadicRadius i)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ x r, 0 < r → r < 1 →
      (μ : Measure Plane) (Metric.closedBall x r) ≤
        ENNReal.ofReal C * ENNReal.ofReal (realGauge θ r) := by
  let Cinf : ℝ≥0∞ := ENNReal.ofReal (realGauge θ (1 / 8))⁻¹ +
    A * 4 * ENNReal.ofReal (gaugeDoublingConstant θ ^ 3)
  have hsmall : 0 < realGauge θ (1 / 8) := realGauge_pos θ (by norm_num)
  have hCfin : Cinf ≠ ∞ := by
    dsimp [Cinf]
    finiteness
  have hCpos : 0 < Cinf :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hsmall)).trans_le (le_add_right le_rfl)
  refine ⟨Cinf.toReal, ENNReal.toReal_pos hCpos.ne' hCfin, ?_⟩
  intro x r hr hr1
  rw [ENNReal.ofReal_toReal hCfin]
  by_cases hreight : r ≤ 1 / 8
  · have hr2 : 0 < 2 * r := by positivity
    obtain ⟨i, hilow, hiup⟩ := exists_dyadicRadius_bracket hr2 (by linarith)
    cases i with
    | zero =>
        have h : (1 : ℝ) / 2 < 2 * r := by simpa [dyadicRadius_eq_half_pow] using hilow
        linarith
    | succ j =>
        have hrcover : 2 * r ≤ dyadicCoverRadius j := by
          rw [dyadicCoverRadius_eq_dyadicRadius_succ]
          exact hiup
        have hscale : dyadicRadius j < 8 * r := by
          rw [dyadicRadius_eq_four_mul_add_two]
          have : dyadicRadius (j + 2) < 2 * r := by
            simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hilow
          linarith
        have hside : ENNReal.ofReal (realGauge θ (dyadicRadius j)) ≤
            ENNReal.ofReal (gaugeDoublingConstant θ ^ 3) * ENNReal.ofReal (realGauge θ r) := by
          have hjone : dyadicRadius j ≤ 1 := by
            cases j with
            | zero => simp [dyadicRadius]
            | succ k => exact (dyadicRadius_le_half (by omega)).trans (by norm_num)
          calc
            ENNReal.ofReal (realGauge θ (dyadicRadius j)) =
                thetaGauge θ (ENNReal.ofReal (dyadicRadius j)) :=
              (thetaGauge_ofReal_le_one hθ₀ (dyadicRadius_pos j).le hjone).symm
            _ ≤ thetaGauge θ (ENNReal.ofReal (8 * r)) :=
              thetaGauge_mono hθ₀.le (ENNReal.ofReal_le_ofReal hscale.le)
            _ = ENNReal.ofReal (realGauge θ (8 * r)) :=
              thetaGauge_ofReal_le_one hθ₀ (by positivity) (by linarith)
            _ ≤ ENNReal.ofReal (gaugeDoublingConstant θ ^ 3 * realGauge θ r) :=
              ENNReal.ofReal_le_ofReal (realGauge_mul_eight_le hθ₀.le hθ₁ hr (by linarith))
            _ = _ := ENNReal.ofReal_mul (pow_nonneg (gaugeDoublingConstant_pos θ).le 3)
        calc
          (μ : Measure Plane) (Metric.closedBall x r) ≤
              (μ : Measure Plane) (Metric.ball x (2 * r)) :=
            measure_mono (Metric.closedBall_subset_ball (by linarith))
          _ ≤ A * (4 * ENNReal.ofReal (realGauge θ (dyadicRadius j))) :=
            hbound j x (2 * r) hr2 hrcover
          _ ≤ (A * 4 * ENNReal.ofReal (gaugeDoublingConstant θ ^ 3)) *
              ENNReal.ofReal (realGauge θ r) := by
            calc
              _ ≤ A * (4 * (ENNReal.ofReal (gaugeDoublingConstant θ ^ 3) *
                  ENNReal.ofReal (realGauge θ r))) := by gcongr
              _ = _ := by ring
          _ ≤ Cinf * ENNReal.ofReal (realGauge θ r) :=
            mul_le_mul_left (le_add_left le_rfl) _
  · have hlarge : realGauge θ (1 / 8) ≤ realGauge θ r :=
      realGauge_mono hθ₀.le (by norm_num) (not_le.mp hreight).le hr1.le
    have hprod : 1 ≤ (realGauge θ (1 / 8))⁻¹ * realGauge θ r := by
      calc
        1 = (realGauge θ (1 / 8))⁻¹ * realGauge θ (1 / 8) :=
          (inv_mul_cancel₀ hsmall.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (inv_pos.mpr hsmall).le
    calc
      (μ : Measure Plane) (Metric.closedBall x r) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal ((realGauge θ (1 / 8))⁻¹ * realGauge θ r) :=
        ENNReal.ofReal_le_ofReal hprod
      _ = ENNReal.ofReal (realGauge θ (1 / 8))⁻¹ * ENNReal.ofReal (realGauge θ r) :=
        ENNReal.ofReal_mul (inv_pos.mpr hsmall).le
      _ ≤ Cinf * ENNReal.ofReal (realGauge θ r) :=
        mul_le_mul_left (le_add_right le_rfl) _

end FalconerThetaGauge.GaugeFrostman

namespace FalconerThetaGauge

/-- Lemma 5.1 of the manuscript: a compact set of positive gauge Hausdorff
measure carries a probability measure with a uniform gauge bound on closed balls.
The result is proved for the stronger parameter range `0 < θ ≤ 1`. -/
theorem exists_gauge_frostman_probabilityMeasure {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    {E : Set Plane} (hE : IsCompact E) (hGauge : 0 < gaugeMeasure θ E) :
    ∃ (μ : ProbabilityMeasure Plane) (C : ℝ),
      0 < C ∧ (μ : Measure Plane) E = 1 ∧ (μ : Measure Plane).support ⊆ E ∧
      ∀ x r, 0 < r → r < 1 → (μ : Measure Plane) (Metric.closedBall x r) ≤
        ENNReal.ofReal C * ENNReal.ofReal (realGauge θ r) := by
  have hcontent := gaugeContent_pos_of_gaugeMeasure_pos hθ₀.le hGauge
  obtain ⟨μ, hμE, hbound⟩ :=
    GaugeFrostman.exists_probabilityMeasure_dyadic_frostman hE hθ₀ hθ₁ hcontent
  have hA : ENNReal.ofReal (gaugeDoublingConstant θ) * (gaugeContent θ E)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hcontent.ne')
  obtain ⟨C, hC, hballs⟩ :=
    GaugeFrostman.closedBall_bound_of_dyadic_ball_bound μ hθ₀ hθ₁ hA hbound
  have hEcompl : (μ : Measure Plane) Eᶜ = 0 := hμE
  have hmass : (μ : Measure Plane) E = 1 := by
    simpa [hEcompl] using prob_add_prob_compl (μ := (μ : Measure Plane)) hE.measurableSet
  have hsupp : (μ : Measure Plane).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed (by rwa [mem_ae_iff])
  exact ⟨μ, C, hC, hmass, hsupp, hballs⟩

end FalconerThetaGauge
