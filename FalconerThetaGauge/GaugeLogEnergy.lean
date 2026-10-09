module

public import FalconerThetaGauge.GaugeFrostmanLimit
public import FalconerThetaGauge.Asymptotics
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Finite logarithmically weighted critical energy

This file proves the finiteness assertion of Corollary 5.5 by summing dyadic
annuli. The inverse distance is taken in the extended nonnegative reals, so the
kernel is infinite on the diagonal. The ball bound implies that the measure
has no atoms, and the diagonal is therefore null in each potential integral.

The annulus decomposition follows `FalconerPacking.Energy` (original source
credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Energy.lean
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The logarithmic weight `L(r) = 1 + log⁺(1/r)`. -/
def logWeight (r : ℝ) : ℝ := 1 + max 0 (Real.log (1 / r))

/-- The radial critical kernel, with the extended inverse at radius zero. -/
def logCriticalRadial (γ r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (logWeight r ^ γ) * (ENNReal.ofReal r)⁻¹

/-- The logarithmically weighted critical kernel. -/
def logCriticalKernel (γ : ℝ) (x y : Plane) : ℝ≥0∞ :=
  logCriticalRadial γ (dist x y)

/-- The logarithmically weighted first energy of the source measure. -/
def logCriticalEnergy (γ : ℝ) (μ : Measure Plane) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, logCriticalKernel γ x y ∂μ ∂μ

/-- The hypothesis of Corollary 5.5, expressed using open balls. -/
def HasGaugeBallBound (μ : Measure Plane) (θ C : ℝ) : Prop :=
  ∀ x r, 0 < r → r < 1 → μ (Metric.ball x r) ≤
    ENNReal.ofReal C * ENNReal.ofReal (realGauge θ r)

@[simp]
theorem logCriticalRadial_zero (γ : ℝ) : logCriticalRadial γ 0 = ∞ := by
  simp [logCriticalRadial, logWeight]

@[simp]
theorem logCriticalKernel_self (γ : ℝ) (x : Plane) : logCriticalKernel γ x x = ∞ := by
  simp [logCriticalKernel]

theorem logCriticalKernel_of_ne (γ : ℝ) {x y : Plane} (hxy : x ≠ y) :
    logCriticalKernel γ x y = ENNReal.ofReal (logWeight (dist x y) ^ γ / dist x y) := by
  rw [ENNReal.ofReal_div_of_pos (dist_pos.mpr hxy), ENNReal.div_eq_inv_mul, mul_comm]
  rfl

theorem logWeight_pos (r : ℝ) : 0 < logWeight r := by
  have := le_max_left (0 : ℝ) (Real.log (1 / r))
  unfold logWeight
  linarith

theorem logCriticalRadial_le {γ r s : ℝ} (hγ : 0 ≤ γ) (hr : 0 < r) (hrs : r ≤ s) :
    logCriticalRadial γ s ≤ logCriticalRadial γ r := by
  have hs : 0 < s := hr.trans_le hrs
  have hlog : Real.log (1 / s) ≤ Real.log (1 / r) :=
    Real.log_le_log (one_div_pos.mpr hs) (one_div_le_one_div_of_le hr hrs)
  have hweight : logWeight s ≤ logWeight r := by
    simpa only [logWeight, add_comm] using add_le_add_left (max_le_max_left 0 hlog) 1
  apply mul_le_mul
  · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (logWeight_pos s).le hweight hγ)
  · exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hrs)
  · exact bot_le
  · exact bot_le

theorem logCriticalRadial_ne_top (γ : ℝ) {r : ℝ} (hr : 0 < r) :
    logCriticalRadial γ r ≠ ∞ := by
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne')

theorem measurable_logCriticalKernel (γ : ℝ) :
    Measurable (fun p : Plane × Plane ↦ logCriticalKernel γ p.1 p.2) := by
  unfold logCriticalKernel logCriticalRadial logWeight
  fun_prop

theorem logCriticalEnergy_eq_lintegral_prod (γ : ℝ) (μ : Measure Plane) [SFinite μ] :
    logCriticalEnergy γ μ =
      ∫⁻ p : Plane × Plane, logCriticalKernel γ p.1 p.2 ∂μ.prod μ :=
  (lintegral_prod _ (measurable_logCriticalKernel γ).aemeasurable).symm

namespace GaugeLogEnergy

open GaugeFrostman

theorem dyadicRadius_succ_lt_one (n : ℕ) : dyadicRadius (n + 1) < 1 :=
  (dyadicRadius_le_half (by omega)).trans_lt (by norm_num)

theorem tendsto_dyadicRadius_succ :
    Tendsto (fun n : ℕ ↦ dyadicRadius (n + 1)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
  simpa only [dyadicRadius_eq_half_pow, pow_succ, zero_mul] using h

/-- The gauge ball bound rules out atoms; this also removes the infinite diagonal. -/
theorem measure_singleton_eq_zero {μ : Measure Plane} {θ C : ℝ} (hC : 0 ≤ C)
    (hball : HasGaugeBallBound μ θ C) (x : Plane) : μ {x} = 0 := by
  have hbound : ∀ n : ℕ, μ {x} ≤ ENNReal.ofReal (C * dyadicRadius (n + 1)) := by
    intro n
    calc
      μ {x} ≤ μ (Metric.ball x (dyadicRadius (n + 1))) :=
        measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self (dyadicRadius_pos _)))
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (realGauge θ (dyadicRadius (n + 1))) :=
        hball x _ (dyadicRadius_pos _) (dyadicRadius_succ_lt_one n)
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (dyadicRadius (n + 1)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal
          (realGauge_le θ (dyadicRadius_pos _).le (dyadicRadius_succ_lt_one n).le)) _
      _ = _ := (ENNReal.ofReal_mul hC).symm
  have hreal := tendsto_dyadicRadius_succ.const_mul C
  have htend := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have htend' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C * dyadicRadius (n + 1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using htend
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto htend' (Eventually.of_forall hbound))

/-- A stretched exponential remains summable after any fixed nonnegative
logarithmic polynomial cost. -/
theorem summable_pow_mul_exp_neg (γ θ c : ℝ) (hγ : 1 ≤ γ) (hθ : 0 < θ) (hc : 0 < c) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ γ * Real.exp (-c * (n : ℝ) ^ θ)) := by
  have hγpos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  apply summable_of_isBigO_nat (summable_exp_neg_mul_nat_rpow θ (c / 2) hθ (by positivity))
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_log_le_mul_rpow θ (c / (2 * γ)) hθ (by positivity),
    eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hlog : γ * Real.log (n : ℝ) ≤ (c / 2) * (n : ℝ) ^ θ := by
    have := mul_le_mul_of_nonneg_left hn hγpos.le
    convert this using 1
    field_simp
  have hbound : (n : ℝ) ^ γ * Real.exp (-c * (n : ℝ) ^ θ) ≤
      Real.exp (-(c / 2) * (n : ℝ) ^ θ) := by
    rw [Real.rpow_def_of_pos hnpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) γ)
      (Real.exp_pos _).le)] using hbound

theorem log_inv_dyadicRadius (n : ℕ) :
    Real.log (1 / dyadicRadius n) = (n : ℝ) * Real.log 2 := by
  rw [one_div, Real.log_inv, dyadicRadius, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  ring

theorem logWeight_dyadicRadius (n : ℕ) :
    logWeight (dyadicRadius n) = 1 + (n : ℝ) * Real.log 2 := by
  rw [logWeight, log_inv_dyadicRadius, max_eq_right
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))]

/-- The summable shell majorant after the critical inverse radius cancels the
linear factor of the gauge. -/
def shellMajorant (γ θ C : ℝ) (n : ℕ) : ℝ :=
  2 * C * (1 + ((n : ℝ) + 2) * Real.log 2) ^ γ *
    Real.exp (-((((n : ℝ) + 1) * Real.log 2) ^ θ))

theorem shellMajorant_nonneg {γ θ C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ shellMajorant γ θ C n := by
  unfold shellMajorant
  positivity

theorem summable_shellMajorant {γ θ C : ℝ} (hγ : 1 ≤ γ) (hθ : 0 < θ) (hC : 0 ≤ C) :
    Summable (shellMajorant γ θ C) := by
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase := summable_pow_mul_exp_neg γ θ (Real.log 2 ^ θ) hγ hθ
    (Real.rpow_pos_of_pos hlogpos _)
  have hshift : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ γ *
      Real.exp (-(Real.log 2 ^ θ) * ((n : ℝ) + 1) ^ θ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hbase
  apply (hshift.mul_left (2 * C * (3 : ℝ) ^ γ)).of_nonneg_of_le
    (shellMajorant_nonneg hC)
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlogle : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hpoly : (1 + ((n : ℝ) + 2) * Real.log 2) ^ γ ≤
      (3 : ℝ) ^ γ * ((n : ℝ) + 1) ^ γ := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity)]
    apply Real.rpow_le_rpow (by positivity)
    · nlinarith
    · exact zero_le_one.trans hγ
  have hexp : Real.exp (-((((n : ℝ) + 1) * Real.log 2) ^ θ)) =
      Real.exp (-(Real.log 2 ^ θ) * ((n : ℝ) + 1) ^ θ) := by
    rw [Real.mul_rpow (by positivity) hlogpos.le]
    congr 1
    ring
  rw [shellMajorant, hexp]
  calc
    _ ≤ 2 * C * ((3 : ℝ) ^ γ * ((n : ℝ) + 1) ^ γ) *
        Real.exp (-(Real.log 2 ^ θ) * ((n : ℝ) + 1) ^ θ) := by gcongr
    _ = _ := by ring

/-- Critical scaling cancels exactly between the annulus kernel and the gauge. -/
theorem shell_kernel_cost_eq (γ θ C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    logCriticalRadial γ (dyadicRadius (n + 2)) *
      (ENNReal.ofReal C * ENNReal.ofReal (realGauge θ (dyadicRadius (n + 1)))) =
        ENNReal.ofReal (shellMajorant γ θ C n) := by
  rw [logCriticalRadial, logWeight_dyadicRadius, ← ENNReal.ofReal_inv_of_pos (dyadicRadius_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
    ← ENNReal.ofReal_mul hC,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by positivity) γ)
      (inv_pos.mpr (dyadicRadius_pos (n + 2))).le)]
  unfold realGauge shellMajorant
  rw [log_inv_dyadicRadius]
  have hratio : (dyadicRadius (n + 2))⁻¹ * dyadicRadius (n + 1) = 2 := by
    rw [dyadicRadius_eq_half_pow, dyadicRadius_eq_half_pow, pow_add, pow_add]
    norm_num
    field_simp
    ring
  congr 1
  push_cast
  calc
    _ = C * ((dyadicRadius (n + 2))⁻¹ * dyadicRadius (n + 1)) *
        (1 + ((n : ℝ) + 2) * Real.log 2) ^ γ *
          Real.exp (-((((n : ℝ) + 1) * Real.log 2) ^ θ)) := by ring
    _ = _ := by rw [hratio]; ring

/-- The gauge ball bound yields a finite logarithmic critical potential,
uniformly in the point at which the potential is evaluated. -/
theorem exists_bound_lintegral_logCriticalKernel {μ : Measure Plane} [IsFiniteMeasure μ]
    {γ θ C : ℝ} (hγ : 1 ≤ γ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (hball : HasGaugeBallBound μ θ C) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x, ∫⁻ y, logCriticalKernel γ x y ∂μ ≤ B := by
  classical
  let B : ℝ≥0∞ := logCriticalRadial γ (1 / 2) * μ univ +
    ∑' n, ENNReal.ofReal (shellMajorant γ θ C n)
  have hB : B ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (logCriticalRadial_ne_top γ (by norm_num)) (measure_ne_top _ _),
      (summable_shellMajorant hγ hθ hC).tsum_ofReal_ne_top⟩
  refine ⟨B, hB, ?_⟩
  intro x
  let A : ℕ → Set Plane := fun n ↦
    Metric.ball x (dyadicRadius (n + 1)) \ Metric.ball x (dyadicRadius (n + 2))
  let F : Set Plane := (Metric.ball x (1 / 2))ᶜ
  have hAmeas : ∀ n, MeasurableSet (A n) :=
    fun n ↦ Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hFmeas : MeasurableSet F := Metric.isOpen_ball.measurableSet.compl
  have hcover : (univ : Set Plane) ⊆ ({x} ∪ ⋃ n, A n) ∪ F := by
    intro y _
    rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h | h
    · exact Or.inl (Or.inl (by simp [dist_eq_zero.mp h.symm]))
    rcases le_or_gt (1 / 2) (dist y x) with hfar | hnear
    · exact Or.inr (by simpa [F, Metric.mem_ball, not_lt] using hfar)
    have hex : ∃ n : ℕ, dyadicRadius (n + 1) ≤ dist y x := by
      obtain ⟨n, hn⟩ := (tendsto_dyadicRadius_succ.eventually (gt_mem_nhds h)).exists
      exact ⟨n, hn.le⟩
    have hspec : dyadicRadius (Nat.find hex + 1) ≤ dist y x := Nat.find_spec hex
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
      · rw [hzero] at hspec
        have : (1 : ℝ) / 2 ≤ dist y x := by
          simpa only [zero_add, dyadicRadius_eq_half_pow, pow_one] using hspec
        exact (not_le_of_gt hnear this).elim
      · exact hpos
    have hmin : ¬dyadicRadius ((Nat.find hex - 1) + 1) ≤ dist y x :=
      Nat.find_min hex (by omega)
    refine Or.inl (Or.inr (mem_iUnion.mpr ⟨Nat.find hex - 1, ?_⟩))
    refine ⟨Metric.mem_ball.mpr (not_le.mp hmin), ?_⟩
    have hinner : Nat.find hex - 1 + 2 = Nat.find hex + 1 := by omega
    rw [hinner]
    exact fun hmem ↦ not_lt_of_ge hspec (Metric.mem_ball.mp hmem)
  have hxzero : μ {x} = 0 := measure_singleton_eq_zero hC hball x
  have hfar : ∫⁻ y in F, logCriticalKernel γ x y ∂μ ≤
      logCriticalRadial γ (1 / 2) * μ univ := by
    calc
      ∫⁻ y in F, logCriticalKernel γ x y ∂μ ≤
          ∫⁻ _y in F, logCriticalRadial γ (1 / 2) ∂μ := by
        refine lintegral_mono_ae ((ae_restrict_iff' hFmeas).mpr (Eventually.of_forall ?_))
        intro y hy
        have hdist : (1 : ℝ) / 2 ≤ dist x y := by
          rw [dist_comm]
          simpa [F, Metric.mem_ball, not_lt] using hy
        exact logCriticalRadial_le (zero_le_one.trans hγ) (by norm_num) hdist
      _ = logCriticalRadial γ (1 / 2) * μ F := setLIntegral_const _ _
      _ ≤ _ := mul_le_mul_right (measure_mono (subset_univ _)) _
  have hann : ∀ n, ∫⁻ y in A n, logCriticalKernel γ x y ∂μ ≤
      ENNReal.ofReal (shellMajorant γ θ C n) := by
    intro n
    calc
      ∫⁻ y in A n, logCriticalKernel γ x y ∂μ ≤
          ∫⁻ _y in A n, logCriticalRadial γ (dyadicRadius (n + 2)) ∂μ := by
        refine lintegral_mono_ae ((ae_restrict_iff' (hAmeas n)).mpr (Eventually.of_forall ?_))
        intro y hy
        apply logCriticalRadial_le (zero_le_one.trans hγ) (dyadicRadius_pos _)
        rw [dist_comm]
        exact not_lt.mp fun hlt ↦ hy.2 (Metric.mem_ball.mpr hlt)
      _ = logCriticalRadial γ (dyadicRadius (n + 2)) * μ (A n) := setLIntegral_const _ _
      _ ≤ logCriticalRadial γ (dyadicRadius (n + 2)) *
          (ENNReal.ofReal C * ENNReal.ofReal (realGauge θ (dyadicRadius (n + 1)))) := by
        gcongr
        exact (measure_mono sdiff_subset).trans
          (hball x _ (dyadicRadius_pos _) (dyadicRadius_succ_lt_one n))
      _ = _ := shell_kernel_cost_eq γ θ C hC n
  calc
    ∫⁻ y, logCriticalKernel γ x y ∂μ = ∫⁻ y in univ, logCriticalKernel γ x y ∂μ := by
      rw [Measure.restrict_univ]
    _ ≤ ∫⁻ y in ({x} ∪ ⋃ n, A n) ∪ F, logCriticalKernel γ x y ∂μ := lintegral_mono_set hcover
    _ ≤ (∫⁻ y in {x} ∪ ⋃ n, A n, logCriticalKernel γ x y ∂μ) +
        ∫⁻ y in F, logCriticalKernel γ x y ∂μ := lintegral_union_le _ _ _
    _ ≤ ((∫⁻ y in {x}, logCriticalKernel γ x y ∂μ) +
        ∫⁻ y in ⋃ n, A n, logCriticalKernel γ x y ∂μ) +
        ∫⁻ y in F, logCriticalKernel γ x y ∂μ := by
      gcongr
      exact lintegral_union_le _ _ _
    _ ≤ (0 + ∑' n, ∫⁻ y in A n, logCriticalKernel γ x y ∂μ) +
        logCriticalRadial γ (1 / 2) * μ univ := by
      gcongr
      · exact le_of_eq (setLIntegral_measure_zero _ _ hxzero)
      · exact lintegral_iUnion_le _ _
    _ ≤ (∑' n, ENNReal.ofReal (shellMajorant γ θ C n)) +
        logCriticalRadial γ (1 / 2) * μ univ := by
      simpa only [zero_add] using add_le_add_left (ENNReal.tsum_le_tsum hann) _
    _ = B := add_comm _ _

end GaugeLogEnergy

/-- Corollary 5.5: a finite measure with the manuscript's gauge ball bound has
finite logarithmically weighted critical energy at every order `γ ≥ 1`. -/
theorem logCriticalEnergy_ne_top_of_hasGaugeBallBound {μ : Measure Plane} [IsFiniteMeasure μ]
    {γ θ C : ℝ} (hγ : 1 ≤ γ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (hball : HasGaugeBallBound μ θ C) : logCriticalEnergy γ μ ≠ ∞ := by
  obtain ⟨B, hB, hbound⟩ := GaugeLogEnergy.exists_bound_lintegral_logCriticalKernel
    hγ hθ hC hball
  have hle : logCriticalEnergy γ μ ≤ B * μ univ := by
    refine (lintegral_mono fun x ↦ hbound x).trans ?_
    rw [lintegral_const]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hB (measure_ne_top _ _)) hle

/-- A single Frostman probability measure obtained from the positive gauge
measure hypothesis has finite logarithmic critical energy at every order. -/
theorem exists_probabilityMeasure_finite_logCriticalEnergy {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) {E : Set Plane} (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) :
    ∃ (μ : ProbabilityMeasure Plane) (C : ℝ),
      0 < C ∧ (μ : Measure Plane) E = 1 ∧ (μ : Measure Plane).support ⊆ E ∧
      HasGaugeBallBound (μ : Measure Plane) θ C ∧
      ∀ γ : ℝ, 1 ≤ γ → logCriticalEnergy γ (μ : Measure Plane) ≠ ∞ := by
  obtain ⟨μ, C, hC, hmass, hsupp, hclosed⟩ :=
    exists_gauge_frostman_probabilityMeasure hθ₀ hθ₁ hE hGauge
  have hball : HasGaugeBallBound (μ : Measure Plane) θ C := by
    intro x r hr hr1
    exact (measure_mono Metric.ball_subset_closedBall).trans (hclosed x r hr hr1)
  exact ⟨μ, C, hC, hmass, hsupp, hball,
    fun γ hγ ↦ logCriticalEnergy_ne_top_of_hasGaugeBallBound hγ hθ₀ hC.le hball⟩

end FalconerThetaGauge
