module

public import FalconerThetaGauge.OrliczEnergyFourier

/-!
# The manuscript's logarithmic Orlicz function

These pointwise inequalities are the concrete transfer step in Theorem 5.4.
All statements use the actual function `t log(exp(1) + t)^γ` on nonnegative
arguments, and the quadratic density weight from Lemma 5.3.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace FalconerThetaGauge

def orliczPhi (γ t : ℝ) : ℝ := t * (Real.log (Real.exp 1 + t)) ^ γ

def orliczQuadratic (γ t : ℝ) : ℝ := t ^ 2 * (Real.log (Real.exp 1 + t)) ^ γ

def orliczPhiENN (γ t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (orliczPhi γ t)

def orliczQuadraticENN (γ t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (orliczQuadratic γ t)

theorem log_exp_one_add_ge_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ Real.log (Real.exp 1 + t) := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ Real.exp 1 + t from le_add_of_nonneg_right ht)
  simpa only [Real.log_exp] using h

theorem orliczPhi_nonneg (γ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ orliczPhi γ t :=
  mul_nonneg ht (Real.rpow_nonneg (zero_le_one.trans (log_exp_one_add_ge_one ht)) γ)

theorem orliczQuadratic_nonneg (γ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ orliczQuadratic γ t :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans (log_exp_one_add_ge_one ht)) γ)

theorem orliczPhi_mono {γ a b : ℝ} (hγ : 0 ≤ γ) (ha : 0 ≤ a) (hab : a ≤ b) :
    orliczPhi γ a ≤ orliczPhi γ b := by
  unfold orliczPhi
  have hw : (Real.log (Real.exp 1 + a)) ^ γ ≤ (Real.log (Real.exp 1 + b)) ^ γ := by
    apply Real.rpow_le_rpow (zero_le_one.trans (log_exp_one_add_ge_one ha)) _ hγ
    exact Real.log_le_log (by positivity) (add_le_add le_rfl hab)
  exact mul_le_mul hab hw
    (Real.rpow_nonneg (zero_le_one.trans (log_exp_one_add_ge_one ha)) γ) (ha.trans hab)

/-- The elementary product inequality used in the Orlicz transfer argument. -/
theorem orlicz_product_le {γ a b : ℝ} (hγ : 0 ≤ γ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    orliczPhi γ a * b ≤ orliczQuadratic γ a + orliczQuadratic γ b := by
  by_cases hba : b ≤ a
  · calc
      orliczPhi γ a * b ≤ orliczPhi γ a * a :=
        mul_le_mul_of_nonneg_left hba (orliczPhi_nonneg γ ha)
      _ = orliczQuadratic γ a := by unfold orliczPhi orliczQuadratic; ring
      _ ≤ _ := le_add_of_nonneg_right (orliczQuadratic_nonneg γ hb)
  · calc
      orliczPhi γ a * b ≤ orliczPhi γ b * b :=
        mul_le_mul_of_nonneg_right (orliczPhi_mono hγ ha (le_of_not_ge hba)) hb
      _ = orliczQuadratic γ b := by unfold orliczPhi orliczQuadratic; ring
      _ ≤ _ := le_add_of_nonneg_left (orliczQuadratic_nonneg γ ha)

/-- Removing a bounded radial distance weight costs the manuscript's explicit factor. -/
theorem orliczPhi_mul_le {γ D t : ℝ} (hγ : 0 ≤ γ) (hD : 1 ≤ D) (ht : 0 ≤ t) :
    orliczPhi γ (D * t) ≤ D * (1 + Real.log D) ^ γ * orliczPhi γ t := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have he : 0 < Real.exp 1 + t := by positivity
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hl : 1 ≤ Real.log (Real.exp 1 + t) := log_exp_one_add_ge_one ht
  have hlog : Real.log (Real.exp 1 + D * t) ≤
      (1 + Real.log D) * Real.log (Real.exp 1 + t) := by
    have harg : Real.exp 1 + D * t ≤ D * (Real.exp 1 + t) := by
      have h := mul_le_mul_of_nonneg_right hD (Real.exp_nonneg 1)
      nlinarith
    have h := Real.log_le_log (by positivity : 0 < Real.exp 1 + D * t) harg
    rw [Real.log_mul hDpos.ne' he.ne'] at h
    nlinarith [mul_le_mul_of_nonneg_left hl hlD]
  have hw : (Real.log (Real.exp 1 + D * t)) ^ γ ≤
      (1 + Real.log D) ^ γ * (Real.log (Real.exp 1 + t)) ^ γ := by
    rw [← Real.mul_rpow (by linarith) (zero_le_one.trans hl)]
    exact Real.rpow_le_rpow (zero_le_one.trans (log_exp_one_add_ge_one (mul_nonneg hDpos.le ht)))
      hlog hγ
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hDpos.le ht)
  simpa only [orliczPhi, mul_assoc, mul_left_comm, mul_comm] using hm

end FalconerThetaGauge
