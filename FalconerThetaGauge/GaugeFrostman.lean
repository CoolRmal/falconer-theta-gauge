module

public import FalconerThetaGauge.Statement
public import FalconerThetaGauge.GaugeFrostmanWeights
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Gauge content and the finite ingredients of Frostman's lemma

These are ingredients of Lemma 5.1 of the manuscript. In particular, positive
gauge Hausdorff measure gives positive unrestricted Hausdorff content. The
probability measure and its ball bound are not yet constructed in this file.

The content-to-measure argument is adapted from `FalconerPacking.Content`
(original source credits Yongxi Lin, Apache 2.0), replacing powers by the manuscript's actual gauge.
Source: `CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Content.lean
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

theorem realGauge_mono {θ r s : ℝ} (hθ : 0 ≤ θ) (hr : 0 ≤ r)
    (hrs : r ≤ s) (hs : s ≤ 1) : realGauge θ r ≤ realGauge θ s := by
  by_cases hrzero : r = 0
  · simp only [hrzero, realGauge_zero]
    exact realGauge_nonneg θ (hr.trans hrs)
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
  have hspos : 0 < s := hrpos.trans_le hrs
  have hlogr : 0 ≤ Real.log (1 / r) := Real.log_nonneg ((one_le_div₀ hrpos).mpr (hrs.trans hs))
  have hlogs : 0 ≤ Real.log (1 / s) := Real.log_nonneg ((one_le_div₀ hspos).mpr hs)
  have hlog : Real.log (1 / s) ≤ Real.log (1 / r) := by
    apply Real.log_le_log (one_div_pos.mpr hspos)
    exact one_div_le_one_div_of_le hrpos hrs
  have hpow : Real.log (1 / s) ^ θ ≤ Real.log (1 / r) ^ θ :=
    Real.rpow_le_rpow hlogs hlog hθ
  exact mul_le_mul hrs (Real.exp_le_exp.mpr (neg_le_neg hpow))
    (Real.exp_pos _).le (hr.trans hrs)

theorem thetaGauge_mono {θ : ℝ} (hθ : 0 ≤ θ) : Monotone (thetaGauge θ) := by
  intro r s hrs
  by_cases hs : s < 1
  · have hr : r < 1 := hrs.trans_lt hs
    simp only [thetaGauge, ite_eq_left hr, ite_eq_left hs]
    apply ENNReal.ofReal_le_ofReal
    have hsreal : s.toReal < 1 := ENNReal.toReal_lt_of_lt_ofReal (by simpa using hs)
    exact realGauge_mono hθ ENNReal.toReal_nonneg
      (ENNReal.toReal_mono hs.ne_top hrs) hsreal.le
  · simp only [thetaGauge, ite_eq_right hs]
    exact (thetaGauge_le θ r).trans hrs

theorem thetaGauge_ofReal_le_one {θ r : ℝ} (hθ : 0 < θ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    thetaGauge θ (ENNReal.ofReal r) = ENNReal.ofReal (realGauge θ r) := by
  rcases hr₁.eq_or_lt with rfl | hr
  · simp [thetaGauge, realGauge, Real.zero_rpow hθ.ne']
  · exact thetaGauge_ofReal θ hr₀ hr

/-- A finite doubling constant, uniform in the radius. -/
def gaugeDoublingConstant (θ : ℝ) : ℝ := 2 * Real.exp (Real.log 2 ^ θ)

theorem gaugeDoublingConstant_pos (θ : ℝ) : 0 < gaugeDoublingConstant θ :=
  mul_pos (by norm_num) (Real.exp_pos _)

theorem two_le_gaugeDoublingConstant (θ : ℝ) : 2 ≤ gaugeDoublingConstant θ := by
  have h : 1 ≤ Real.exp (Real.log 2 ^ θ) :=
    Real.one_le_exp_iff.mpr (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) θ)
  simpa [gaugeDoublingConstant] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

/-- Subadditivity of the logarithmic power supplies a radius-independent doubling bound. -/
theorem realGauge_double_le {θ r : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hr : 0 < r) (hrhalf : 2 * r ≤ 1) :
    realGauge θ (2 * r) ≤ gaugeDoublingConstant θ * realGauge θ r := by
  have hlog : 0 ≤ Real.log (1 / (2 * r)) :=
    Real.log_nonneg ((one_le_div₀ (by positivity : (0 : ℝ) < 2 * r)).mpr hrhalf)
  have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogeq : Real.log (1 / r) = Real.log (1 / (2 * r)) + Real.log 2 := by
    simp only [one_div, Real.log_inv, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr.ne']
    ring
  have hpow : Real.log (1 / r) ^ θ ≤ Real.log (1 / (2 * r)) ^ θ + Real.log 2 ^ θ := by
    rw [hlogeq]
    exact Real.rpow_add_le_add_rpow hlog hlogtwo hθ₀ hθ₁
  have hexp : Real.exp (-(Real.log (1 / (2 * r))) ^ θ) ≤
      Real.exp (Real.log 2 ^ θ) * Real.exp (-(Real.log (1 / r)) ^ θ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    realGauge θ (2 * r) ≤
        (2 * r) * (Real.exp (Real.log 2 ^ θ) * Real.exp (-(Real.log (1 / r)) ^ θ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = gaugeDoublingConstant θ * realGauge θ r := by
      unfold gaugeDoublingConstant realGauge
      ring

/-- The cost of a cover piece, with zero cost assigned to the empty set. -/
def gaugeContentCost (θ : ℝ) (s : Set Plane) : ℝ≥0∞ :=
  ⨆ _ : s.Nonempty, thetaGauge θ (Metric.ediam s)

@[simp]
theorem gaugeContentCost_empty (θ : ℝ) : gaugeContentCost θ ∅ = 0 := by
  simp [gaugeContentCost]

/-- Unrestricted Hausdorff content for the logarithmic gauge. -/
def gaugeContent (θ : ℝ) : OuterMeasure Plane :=
  OuterMeasure.ofFunction (gaugeContentCost θ) (gaugeContentCost_empty θ)

theorem gaugeContent_apply (θ : ℝ) (E : Set Plane) :
    gaugeContent θ E =
      ⨅ (t : ℕ → Set Plane) (_ : E ⊆ Set.iUnion t), ∑' n, gaugeContentCost θ (t n) :=
  OuterMeasure.ofFunction_apply _ _ _

theorem gaugeContent_le_gaugeContentCost (θ : ℝ) (E : Set Plane) :
    gaugeContent θ E ≤ gaugeContentCost θ E := OuterMeasure.ofFunction_le _

theorem gaugeContent_le_of_cover {θ : ℝ} {E : Set Plane} {t : ℕ → Set Plane}
    (ht : E ⊆ Set.iUnion t) : gaugeContent θ E ≤ ∑' n, gaugeContentCost θ (t n) := by
  rw [gaugeContent_apply]
  exact iInf_le_of_le t (iInf_le _ ht)

theorem gaugeContent_le_gaugeMeasure (θ : ℝ) (E : Set Plane) :
    gaugeContent θ E ≤ gaugeMeasure θ E := by
  rw [gaugeMeasure_apply]
  refine le_trans ?_ (le_iSup_of_le (1 : ℝ≥0∞) (le_iSup_of_le zero_lt_one le_rfl))
  refine le_iInf fun t ↦ le_iInf fun ht ↦ le_iInf fun _ ↦ ?_
  exact gaugeContent_le_of_cover ht

/-- Vanishing content forces vanishing gauge Hausdorff measure. Efficient
covers have uniformly small diameters because the gauge is positive and increasing. -/
theorem gaugeMeasure_eq_zero_of_gaugeContent_eq_zero {θ : ℝ} (hθ : 0 ≤ θ)
    {E : Set Plane} (hE : gaugeContent θ E = 0) : gaugeMeasure θ E = 0 := by
  refine nonpos_iff_eq_zero.mp (ENNReal.le_of_forall_pos_le_add fun ε hεpos _ ↦ ?_)
  have hε : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hεpos
  rw [zero_add, gaugeMeasure_apply]
  refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
  let δ : ℝ≥0∞ := min ε (thetaGauge θ r)
  have hδpos : 0 < δ := lt_min hε (thetaGauge_pos θ hr)
  have hlt : gaugeContent θ E < δ := by rw [hE]; exact hδpos
  rw [gaugeContent_apply, iInf_lt_iff] at hlt
  obtain ⟨t, ht⟩ := hlt
  rw [iInf_lt_iff] at ht
  obtain ⟨hcov, hcost⟩ := ht
  have hsmall : ∀ n, Metric.ediam (t n) ≤ r := by
    intro n
    rcases Set.eq_empty_or_nonempty (t n) with hempty | hne
    · simp [hempty]
    · by_contra hcon
      have hterm : thetaGauge θ (Metric.ediam (t n)) ≤ ∑' m, gaugeContentCost θ (t m) :=
        (le_iSup (fun _ : (t n).Nonempty ↦ thetaGauge θ (Metric.ediam (t n))) hne).trans
          (show gaugeContentCost θ (t n) ≤ ∑' m, gaugeContentCost θ (t m)
            from ENNReal.le_tsum (f := fun m ↦ gaugeContentCost θ (t m)) n)
      have hge : thetaGauge θ r ≤ thetaGauge θ (Metric.ediam (t n)) :=
        thetaGauge_mono hθ (not_le.mp hcon).le
      exact (not_lt_of_ge (min_le_right (ε : ℝ≥0∞) (thetaGauge θ r)))
        (hcost.trans_le' (hge.trans hterm))
  refine le_trans (iInf_le_of_le t (iInf_le_of_le hcov (iInf_le _ hsmall))) ?_
  exact hcost.le.trans (min_le_left _ _)

/-- The content lower bound needed to prevent finite Frostman masses from vanishing. -/
theorem gaugeContent_pos_of_gaugeMeasure_pos {θ : ℝ} (hθ : 0 ≤ θ) {E : Set Plane}
    (hE : 0 < gaugeMeasure θ E) : 0 < gaugeContent θ E := by
  by_contra h
  have hc : gaugeContent θ E = 0 := nonpos_iff_eq_zero.mp (not_lt.mp h)
  exact hE.ne' (gaugeMeasure_eq_zero_of_gaugeContent_eq_zero hθ hc)

namespace GaugeFrostman

/-- Side length of a dyadic square of generation `j`. -/
def dyadicRadius (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℝ))

theorem dyadicRadius_pos (j : ℕ) : 0 < dyadicRadius j :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem dyadicRadius_le_half {j : ℕ} (hj : 1 ≤ j) : dyadicRadius j ≤ 1 / 2 := by
  have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show -(j : ℝ) ≤ -1 by linarith)
  simpa [dyadicRadius, Real.rpow_neg_one] using h

/-- The actual manuscript gauge, used as the generation capacities of the finite tree. -/
def thetaCapacity (θ : ℝ) : PositiveCapacity where
  value j := realGauge θ (dyadicRadius j)
  positive j := realGauge_pos θ (dyadicRadius_pos j)

/-- The finite normalization construction for the stretched logarithmic gauge.
Every depth produces weights satisfying all dyadic bounds and a cover whose
gauge cost is at most the remaining total weight. -/
theorem exists_finite_gauge_weights (θ : ℝ) (S : Finset (Fin 2 → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) {E : Set Plane} (hcov : E ⊆ ⋃ k' ∈ S, dyadicCube n k') :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (F : Finset (ℕ × (Fin 2 → ℤ))),
      (∀ k, 0 ≤ w k) ∧
      (∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ realGauge θ (dyadicRadius i)) ∧
      (∀ p ∈ F, p.1 ≤ n) ∧
      (E ⊆ ⋃ p ∈ F, dyadicCube p.1 p.2) ∧
      (∑ p ∈ F, realGauge θ (dyadicRadius p.1) ≤ ∑ k' ∈ S, w k') :=
  exists_capacity_weights S hn (thetaCapacity θ) hcov

end GaugeFrostman

end FalconerThetaGauge
