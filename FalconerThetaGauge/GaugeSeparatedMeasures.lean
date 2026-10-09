/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.GaugeLogEnergy

/-!
# Separated compact pieces and their normalized measures

This file proves the geometric selection and normalization used at the start
of Proposition 5.6. It obtains two positive compact pieces from the constructed
gauge Frostman measure, rather than assuming the existence of separated pieces.
The restrictions retain the gauge bound and finite logarithmic critical energies.

The local positivity and normalization arguments are adapted from
`FalconerPacking.Extraction` and `FalconerPacking.Restriction` (original source
credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerThetaGauge

namespace GaugeSeparatedMeasures

/-- The literal normalized restriction; its nonzero finite mass is supplied at each use. -/
def normalizedRestrict (μ : Measure Plane) (K : Set Plane) : Measure Plane :=
  (μ K)⁻¹ • μ.restrict K

theorem normalizedRestrict_apply (μ : Measure Plane) (K A : Set Plane)
    (hA : MeasurableSet A) :
    normalizedRestrict μ K A = (μ K)⁻¹ * μ (A ∩ K) := by
  rw [normalizedRestrict, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]

theorem isProbabilityMeasure_normalizedRestrict {μ : Measure Plane} {K : Set Plane}
    (hμK : μ K ≠ 0) (hμKfin : μ K ≠ ∞) :
    IsProbabilityMeasure (normalizedRestrict μ K) := by
  constructor
  rw [normalizedRestrict_apply μ K univ MeasurableSet.univ, univ_inter,
    ENNReal.inv_mul_cancel hμK hμKfin]

theorem normalizedRestrict_compl {μ : Measure Plane} {K : Set Plane}
    (hK : MeasurableSet K) : normalizedRestrict μ K Kᶜ = 0 := by
  rw [normalizedRestrict_apply μ K Kᶜ hK.compl]
  simp

theorem normalizedRestrict_support_subset {μ : Measure Plane} {K : Set Plane}
    (hK : IsClosed K) : (normalizedRestrict μ K).support ⊆ K := by
  apply Measure.support_subset_of_isClosed hK
  rw [mem_ae_iff]
  exact normalizedRestrict_compl hK.measurableSet

theorem normalizedRestrict_ball_le (μ : Measure Plane) (K : Set Plane) (x : Plane) (r : ℝ) :
    normalizedRestrict μ K (Metric.ball x r) ≤ (μ K)⁻¹ * μ (Metric.ball x r) := by
  rw [normalizedRestrict_apply μ K _ Metric.isOpen_ball.measurableSet]
  exact mul_le_mul_right (measure_mono inter_subset_left) _

/-- Restriction normalization divides the gauge constant by the actual positive mass. -/
theorem hasGaugeBallBound_normalizedRestrict {μ : Measure Plane} {K : Set Plane} {θ C : ℝ}
    (hball : HasGaugeBallBound μ θ C) (hμK : μ K ≠ 0) (hμKfin : μ K ≠ ∞) :
    HasGaugeBallBound (normalizedRestrict μ K) θ (C / (μ K).toReal) := by
  intro x r hr hr1
  have hpos : 0 < (μ K).toReal := ENNReal.toReal_pos hμK hμKfin
  refine (normalizedRestrict_ball_le μ K x r).trans ?_
  refine (mul_le_mul_right (hball x r hr hr1) _).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal hμKfin,
    ENNReal.div_eq_inv_mul, mul_assoc]

/-- A positive-mass set contains a point with positive mass in every relative ball. -/
theorem exists_mem_forall_measure_ball_pos {μ : Measure Plane} {K : Set Plane}
    (hμK : 0 < μ K) : ∃ x ∈ K, ∀ r > 0, 0 < μ (K ∩ Metric.ball x r) := by
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_forall, not_lt, nonpos_iff_eq_zero] at hcon
  have hnull : μ K = 0 := by
    refine measure_null_of_locally_null K fun x hx ↦ ?_
    obtain ⟨r, hr, hzero⟩ := hcon x hx
    refine ⟨K ∩ Metric.ball x r, ?_, hzero⟩
    refine mem_nhdsWithin.mpr
      ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
    intro y hy
    exact ⟨hy.2, hy.1⟩
  exact hμK.ne' hnull

/-- Two relative mass-support points give small positive compact pieces. Their
radius is one two-hundredth of their center separation. -/
theorem exists_positive_compact_ball_pair {μ : Measure Plane} {K : Set Plane}
    (hK : IsCompact K) (hμK : 0 < μ K) (hatom : ∀ x, μ {x} = 0) :
    ∃ (a b : Plane) (A B : Set Plane),
      a ∈ K ∧ b ∈ K ∧ a ≠ b ∧ IsCompact A ∧ IsCompact B ∧
      A ⊆ K ∧ B ⊆ K ∧ 0 < μ A ∧ 0 < μ B ∧
      A ⊆ Metric.closedBall a (dist a b / 200) ∧
      B ⊆ Metric.closedBall b (dist a b / 200) ∧
      ∀ x ∈ A, ∀ y ∈ B,
        (99 / 100 : ℝ) * dist a b ≤ dist x y ∧
          dist x y ≤ (101 / 100 : ℝ) * dist a b := by
  obtain ⟨a, ha, haball⟩ := exists_mem_forall_measure_ball_pos hμK
  have hdiff : 0 < μ (K \ {a}) := by
    rwa [measure_sdiff_null (hatom a)]
  obtain ⟨b, hb, hbball⟩ := exists_mem_forall_measure_ball_pos hdiff
  have hab : a ≠ b := by
    intro h
    exact hb.2 (by simp [h])
  have hd : 0 < dist a b := dist_pos.mpr hab
  have hr : 0 < dist a b / 200 := by positivity
  let A := K ∩ Metric.closedBall a (dist a b / 200)
  let B := K ∩ Metric.closedBall b (dist a b / 200)
  refine ⟨a, b, A, B, ha, hb.1, hab,
    hK.inter_right Metric.isClosed_closedBall, hK.inter_right Metric.isClosed_closedBall,
    inter_subset_left, inter_subset_left, ?_, ?_, inter_subset_right, inter_subset_right, ?_⟩
  · exact (haball _ hr).trans_le
      (measure_mono (inter_subset_inter_right _ Metric.ball_subset_closedBall))
  · exact (hbball _ hr).trans_le (measure_mono fun x hx ↦
      ⟨hx.1.1, Metric.ball_subset_closedBall hx.2⟩)
  · intro x hx y hy
    have hxa : dist x a ≤ dist a b / 200 := Metric.mem_closedBall.mp hx.2
    have hyb : dist y b ≤ dist a b / 200 := Metric.mem_closedBall.mp hy.2
    have hlow := dist_triangle4 a x y b
    have hupp := dist_triangle4 x a b y
    rw [dist_comm a x] at hlow
    rw [dist_comm b y] at hupp
    constructor <;> linarith

/-- A compact positive-mass set for a gauge Frostman measure produces two
separated compact pieces and normalized probabilities with all logarithmic energies finite. -/
theorem exists_normalized_separated_measures {μ : Measure Plane} [IsFiniteMeasure μ]
    {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hball : HasGaugeBallBound μ θ C)
    {K : Set Plane} (hK : IsCompact K) (hμK : 0 < μ K) :
    ∃ (A B : Set Plane) (ν₁ ν₂ : ProbabilityMeasure Plane) (C₁ C₂ d : ℝ),
      IsCompact A ∧ IsCompact B ∧ A ⊆ K ∧ B ⊆ K ∧
      (ν₁ : Measure Plane) = normalizedRestrict μ A ∧
      (ν₂ : Measure Plane) = normalizedRestrict μ B ∧
      C₁ = C / (μ A).toReal ∧ C₂ = C / (μ B).toReal ∧
      0 < C₁ ∧ 0 < C₂ ∧ 0 < d ∧
      (ν₁ : Measure Plane) A = 1 ∧ (ν₂ : Measure Plane) B = 1 ∧
      (ν₁ : Measure Plane).support ⊆ A ∧ (ν₂ : Measure Plane).support ⊆ B ∧
      (∀ x ∈ A, ∀ y ∈ B, d ≤ dist x y) ∧
      HasGaugeBallBound (ν₁ : Measure Plane) θ C₁ ∧
      HasGaugeBallBound (ν₂ : Measure Plane) θ C₂ ∧
      ∀ γ : ℝ, 1 ≤ γ →
        logCriticalEnergy γ (ν₁ : Measure Plane) ≠ ∞ ∧
          logCriticalEnergy γ (ν₂ : Measure Plane) ≠ ∞ := by
  obtain ⟨a, b, A, B, _, _, hab, hA, hB, hAK, hBK, hμA, hμB, _, _, hsep⟩ :=
    exists_positive_compact_ball_pair hK hμK
      (GaugeLogEnergy.measure_singleton_eq_zero hC.le hball)
  have := isProbabilityMeasure_normalizedRestrict hμA.ne' (measure_ne_top μ A)
  have := isProbabilityMeasure_normalizedRestrict hμB.ne' (measure_ne_top μ B)
  let ν₁ : ProbabilityMeasure Plane := ⟨normalizedRestrict μ A, inferInstance⟩
  let ν₂ : ProbabilityMeasure Plane := ⟨normalizedRestrict μ B, inferInstance⟩
  have hC₁ : 0 < C / (μ A).toReal :=
    div_pos hC (ENNReal.toReal_pos hμA.ne' (measure_ne_top μ A))
  have hC₂ : 0 < C / (μ B).toReal :=
    div_pos hC (ENNReal.toReal_pos hμB.ne' (measure_ne_top μ B))
  have hball₁ := hasGaugeBallBound_normalizedRestrict hball hμA.ne' (measure_ne_top μ A)
  have hball₂ := hasGaugeBallBound_normalizedRestrict hball hμB.ne' (measure_ne_top μ B)
  refine ⟨A, B, ν₁, ν₂, C / (μ A).toReal, C / (μ B).toReal,
    (99 / 100 : ℝ) * dist a b, hA, hB, hAK, hBK, rfl, rfl, rfl, rfl,
    hC₁, hC₂, mul_pos (by norm_num) (dist_pos.mpr hab), ?_, ?_,
    normalizedRestrict_support_subset hA.isClosed,
    normalizedRestrict_support_subset hB.isClosed,
    fun x hx y hy ↦ (hsep x hx y hy).1, hball₁, hball₂, ?_⟩
  · change normalizedRestrict μ A A = 1
    rw [normalizedRestrict_apply μ A A hA.measurableSet, inter_self,
      ENNReal.inv_mul_cancel hμA.ne' (measure_ne_top μ A)]
  · change normalizedRestrict μ B B = 1
    rw [normalizedRestrict_apply μ B B hB.measurableSet, inter_self,
      ENNReal.inv_mul_cancel hμB.ne' (measure_ne_top μ B)]
  · intro γ hγ
    exact ⟨logCriticalEnergy_ne_top_of_hasGaugeBallBound hγ hθ hC₁.le hball₁,
      logCriticalEnergy_ne_top_of_hasGaugeBallBound hγ hθ hC₂.le hball₂⟩

end GaugeSeparatedMeasures

/-- The positive gauge Hausdorff measure hypothesis supplies actual separated
probability measures with a common gauge constant and finite energies of every order. -/
theorem exists_separated_probabilityMeasures_finite_logCriticalEnergy {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) {E : Set Plane} (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) :
    ∃ (S₁ S₂ : Set Plane) (μ₁ μ₂ : ProbabilityMeasure Plane) (C d : ℝ),
      IsCompact S₁ ∧ IsCompact S₂ ∧ S₁ ⊆ E ∧ S₂ ⊆ E ∧ 0 < C ∧ 0 < d ∧
      (μ₁ : Measure Plane) S₁ = 1 ∧ (μ₂ : Measure Plane) S₂ = 1 ∧
      (μ₁ : Measure Plane).support ⊆ S₁ ∧ (μ₂ : Measure Plane).support ⊆ S₂ ∧
      (∀ x ∈ S₁, ∀ y ∈ S₂, d ≤ dist x y) ∧
      HasGaugeBallBound (μ₁ : Measure Plane) θ C ∧
      HasGaugeBallBound (μ₂ : Measure Plane) θ C ∧
      ∀ γ : ℝ, 1 ≤ γ →
        logCriticalEnergy γ (μ₁ : Measure Plane) ≠ ∞ ∧
          logCriticalEnergy γ (μ₂ : Measure Plane) ≠ ∞ := by
  obtain ⟨μ, C, hC, hmass, _, hball, _⟩ :=
    exists_probabilityMeasure_finite_logCriticalEnergy hθ₀ hθ₁ hE hGauge
  obtain ⟨A, B, ν₁, ν₂, C₁, C₂, d, hA, hB, hAE, hBE, _, _, _, _, hC₁, hC₂,
    hd, hmass₁, hmass₂, hsupp₁, hsupp₂, hsep, hball₁, hball₂, henergy⟩ :=
    GaugeSeparatedMeasures.exists_normalized_separated_measures hθ₀ hC hball hE
      (by rw [hmass]; exact zero_lt_one)
  refine ⟨A, B, ν₁, ν₂, max C₁ C₂, d, hA, hB, hAE, hBE,
    hC₁.trans_le (le_max_left _ _), hd, hmass₁, hmass₂, hsupp₁, hsupp₂, hsep,
    ?_, ?_, henergy⟩
  · intro x r hr hr1
    exact (hball₁ x r hr hr1).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left C₁ C₂)) _)
  · intro x r hr hr1
    exact (hball₂ x r hr hr1).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right C₁ C₂)) _)

end FalconerThetaGauge
