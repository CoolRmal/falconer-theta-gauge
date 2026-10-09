module

public import FalconerThetaGauge.DirectionalTestsWidening
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Actual mask derivatives vanish at failing narrower-width directions -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff Topology

namespace FalconerThetaGauge

/-- Every angular derivative of the actual smooth mask vanishes outside its
closed doubled arc neighborhood, without any regularity assumption on its passing set. -/
theorem iteratedDeriv_circlePassingMask_eq_zero (K k : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (Z : Set UnitCircle) {θ : ℝ}
    (hθ : unitCircleOfAngle θ ∉ closedArcNeighborhood (2 * δ) Z) :
    iteratedDeriv k (fun t ↦ circlePassingMask K δ Z (unitCircleOfAngle t)) θ = 0 := by
  have hnot : θ ∉ Metric.cthickening (2 * δ) (angularPassingSet Z) :=
    fun ht ↦ hθ ⟨θ, ht, rfl⟩
  have hzero : (fun t ↦ circlePassingMask K δ Z (unitCircleOfAngle t)) =ᶠ[𝓝 θ]
      (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds hnot] with t ht
    rw [circlePassingMask_comp_angle]
    exact explicitPassingMask_eq_zero K hδ _ ht
  simpa only [iteratedDeriv_fun_const_zero] using
    Filter.EventuallyEq.iteratedDeriv_eq k hzero

/-- Lemma 6.7's full derivative-vanishing conclusion for the literal scheduled tests. -/
theorem iteratedDeriv_scheduledCircleMask_eq_zero_of_failure
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {width width' : ℝ}
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (K k : ℕ) (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P) {θ : ℝ}
    (hθ : unitCircleOfAngle θ ∉ scheduledPassingDirections ρ E width' test P) :
    iteratedDeriv k (fun t ↦ scheduledCircleMask ρ E width test K P
      (unitCircleOfAngle t)) θ = 0 := by
  apply iteratedDeriv_circlePassingMask_eq_zero K k (scheduledMaskScale_pos E test)
  intro hw
  exact hθ (closedArcNeighborhood_scheduledPassing_subset ρ E hgap test htube hprojection P hP hw)

/-- The literal equally spaced widths from Definition 6.8. -/
def directionalLevelWidth (I i : ℕ) : ℝ := 2 - (i : ℝ) / I

theorem directionalLevelWidth_gap {I : ℕ} (_hI : 0 < I) (i : ℕ) :
    directionalLevelWidth I i - directionalLevelWidth I (i + 1) = 1 / (I : ℝ) := by
  unfold directionalLevelWidth
  push_cast
  ring

theorem directionalLevelWidth_mem_Icc {I : ℕ} (hI : 0 < I) {i : ℕ} (hi : i ≤ I) :
    directionalLevelWidth I i ∈ Icc 1 2 := by
  have hI' : 0 < (I : ℝ) := by exact_mod_cast hI
  have hi' : (i : ℝ) ≤ I := by exact_mod_cast hi
  have hdiv : (i : ℝ) / I ≤ 1 := (div_le_one hI').mpr hi'
  have hnonneg : 0 ≤ (i : ℝ) / I := by positivity
  constructor <;> dsimp [directionalLevelWidth] <;> linarith

/-- The level spacing has the exact width gap required for literal test stability. -/
theorem directionalLevelWidth_gap_ge {I : ℕ} (hI : 0 < I) (E : ℝ)
    (hsize : (I : ℝ) ≤ (2 : ℝ) ^ E / 8) (i : ℕ) :
    8 * (2 : ℝ) ^ (-E) ≤ directionalLevelWidth I i - directionalLevelWidth I (i + 1) := by
  rw [directionalLevelWidth_gap hI]
  have hI' : 0 < (I : ℝ) := by exact_mod_cast hI
  have hpow : 0 < (2 : ℝ) ^ E := by positivity
  rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hpow hI').mpr
  nlinarith

/-- L2 for every actual level mask: any nonzero angular derivative certifies
passing the next, narrower test at that same occupied anchor. -/
theorem scheduled_level_derivative_ne_zero_implies_passing
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (E : ℝ) {I : ℕ} (hI : 0 < I)
    (hsize : (I : ℝ) ≤ (2 : ℝ) ^ E / 8) (i : ℕ) (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (K k : ℕ) (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P) {θ : ℝ}
    (hθ : iteratedDeriv k (fun t ↦ scheduledCircleMask ρ E (directionalLevelWidth I i)
      test K P (unitCircleOfAngle t)) θ ≠ 0) :
    unitCircleOfAngle θ ∈ scheduledPassingDirections ρ E (directionalLevelWidth I (i + 1))
      test P := by
  by_contra hfail
  exact hθ (iteratedDeriv_scheduledCircleMask_eq_zero_of_failure ρ E
    (directionalLevelWidth_gap_ge hI E hsize i) test htube hprojection K k P hP hfail)

/-- L3 with the literal source arc radius: passing at one level remains passing
at the next throughout `2^(-ℓ) R^(ε/2)`. -/
theorem scheduled_level_passing_neighborhood (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {E : ℝ} (hE : 0 ≤ E) {I : ℕ} (hI : 0 < I)
    (hsize : (I : ℝ) ≤ (2 : ℝ) ^ E / 8) (i : ℕ) (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ test.anchor P)
    {w₀ : UnitCircle} (hw₀ : w₀ ∈ scheduledPassingDirections ρ E (directionalLevelWidth I i)
      test P) :
    closedArcNeighborhood ((2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ (E / 2)) {w₀} ⊆
      scheduledPassingDirections ρ E (directionalLevelWidth I (i + 1)) test P := by
  intro w hw
  obtain ⟨v, hv, hwv⟩ := exists_mem_norm_sub_lt_radius_of_closedArcNeighborhood
    (by positivity : 0 < (2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ (E / 2)) hw
  have heq : v = w₀ := Set.mem_singleton_iff.mp hv
  subst v
  have hpow : (2 : ℝ) ^ (E / 2) ≤ (2 : ℝ) ^ E :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hscale : (2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ (E / 2) ≤
      2 * ((2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ E) := by
    have h : (2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ (E / 2) ≤
        (2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ E :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have hnonneg : 0 ≤ (2 : ℝ) ^ (-(test.length : ℝ)) * (2 : ℝ) ^ E := by positivity
    linarith
  exact (scheduledDirectionalCount_le_of_norm_sub_scale ρ E
    (directionalLevelWidth_gap_ge hI E hsize i) test htube hprojection P hP
      (hwv.le.trans hscale)).trans hw₀

end FalconerThetaGauge
