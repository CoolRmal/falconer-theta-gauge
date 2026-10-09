module

public import FalconerThetaGauge.MaskedDistanceEnergyOrderedLists
public import FalconerThetaGauge.DirectionalTestsPiecesDerivatives
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Literal normalized angular derivatives through the full symbol order budget -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical ContDiff

namespace FalconerThetaGauge

/-- The exact derivative normalization in Definition 6.10. -/
def symbolDerivativeNormalization (δ : ℝ) (k : ℕ) : ℝ :=
  δ ^ k / ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2)

theorem symbolDerivativeNormalization_pos {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    0 < symbolDerivativeNormalization δ k := by
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  unfold symbolDerivativeNormalization
  positivity

theorem symbolDerivativeNormalization_zero (δ : ℝ) :
    symbolDerivativeNormalization δ 0 = 1 := by
  simp [symbolDerivativeNormalization]

theorem symbolDerivativeNormalization_succ {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    symbolDerivativeNormalization δ k =
      (δ⁻¹ * (Real.pi ^ 2 / 6) * ((k + 1 : ℕ) : ℝ) ^ 2) *
        symbolDerivativeNormalization δ (k + 1) := by
  have hf : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold symbolDerivativeNormalization
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- A genuine normalized derivative of the smooth periodic angular mask. -/
def normalizedCircleMaskDerivative (K k : ℕ) (δ : ℝ) (Z : Set UnitCircle) : UnitCircle → ℝ :=
  fun w ↦ symbolDerivativeNormalization δ k *
    iteratedDeriv k (explicitPassingMask K δ (angularPassingSet Z)) (circleAngle w)

theorem periodic_iteratedDeriv {f : ℝ → ℝ} {p : ℝ} (hf : Periodic f p) (k : ℕ) :
    Periodic (iteratedDeriv k f) p := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    intro x
    have heq : (fun y ↦ iteratedDeriv k f (y + p)) = iteratedDeriv k f := funext ih
    rw [← deriv_comp_add_const, heq]

theorem normalizedCircleMaskDerivative_comp_angle (K k : ℕ) (δ : ℝ)
    (Z : Set UnitCircle) (θ : ℝ) :
    normalizedCircleMaskDerivative K k δ Z (unitCircleOfAngle θ) =
      symbolDerivativeNormalization δ k *
        iteratedDeriv k (explicitPassingMask K δ (angularPassingSet Z)) θ := by
  rw [normalizedCircleMaskDerivative, circleAngle_unitCircleOfAngle,
    periodic_apply_toIocMod
      (periodic_iteratedDeriv (explicitPassingMask_periodic K δ
        (angularPassingSet_periodic Z)) k)]

theorem normalizedCircleMaskDerivative_zero (K : ℕ) (δ : ℝ) (Z : Set UnitCircle)
    (w : UnitCircle) : normalizedCircleMaskDerivative K 0 δ Z w =
      circlePassingMask K δ Z w := by
  simp only [normalizedCircleMaskDerivative, symbolDerivativeNormalization_zero,
    iteratedDeriv_zero, one_mul, circlePassingMask]

theorem measurable_normalizedCircleMaskDerivative (K k : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (Z : Set UnitCircle) : Measurable (normalizedCircleMaskDerivative K k δ Z) := by
  have hm := (contDiff_iteratedDeriv_infty
    (contDiff_explicitPassingMask K hδ (angularPassingSet Z)) k).continuous.measurable
  exact measurable_const.mul (hm.comp measurable_circleAngle)

theorem contDiff_normalizedCircleMaskDerivative_comp_angle (K k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (Z : Set UnitCircle) :
    ContDiff ℝ ∞ (fun θ ↦ normalizedCircleMaskDerivative K k δ Z (unitCircleOfAngle θ)) := by
  simp_rw [normalizedCircleMaskDerivative_comp_angle]
  exact contDiff_const.mul
    (contDiff_iteratedDeriv_infty (contDiff_explicitPassingMask K hδ _) k)

theorem norm_normalizedCircleMaskDerivative_le_one (K k : ℕ) (hk : k ≤ K)
    {δ : ℝ} (hδ : 0 < δ) (Z : Set UnitCircle) (w : UnitCircle) :
    ‖normalizedCircleMaskDerivative K k δ Z w‖ ≤ 1 := by
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hp : 0 < (Real.pi ^ 2 / 6) ^ k := by positivity
  rw [normalizedCircleMaskDerivative, norm_mul, Real.norm_of_nonneg
    (symbolDerivativeNormalization_pos hδ k).le]
  calc
    _ ≤ symbolDerivativeNormalization δ k *
        (δ⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedDeriv_explicitPassingMask_le K k hk hδ _ _)
          (symbolDerivativeNormalization_pos hδ k).le
    _ = 1 := by
      unfold symbolDerivativeNormalization
      rw [inv_pow]
      field_simp

theorem deriv_normalizedCircleMaskDerivative_comp_angle (K k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (Z : Set UnitCircle) (θ : ℝ) :
    deriv (fun t ↦ normalizedCircleMaskDerivative K k δ Z (unitCircleOfAngle t)) θ =
      (δ⁻¹ * (Real.pi ^ 2 / 6) * ((k + 1 : ℕ) : ℝ) ^ 2) *
        normalizedCircleMaskDerivative K (k + 1) δ Z (unitCircleOfAngle θ) := by
  simp_rw [normalizedCircleMaskDerivative_comp_angle]
  rw [deriv_const_mul_field, ← iteratedDeriv_succ, symbolDerivativeNormalization_succ hδ k]
  ring

theorem symbol_oneStep_coefficient_le {T k : ℕ} (hk : k + 1 ≤ 8 * T) :
    (Real.pi ^ 2 / 6) * ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 128 * (T : ℝ) ^ 2 := by
  have hk' : ((k + 1 : ℕ) : ℝ) ≤ 8 * (T : ℝ) := by exact_mod_cast hk
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  calc
    _ ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
    _ ≤ 2 * (8 * (T : ℝ)) ^ 2 := by gcongr
    _ = _ := by ring

theorem explicitDerivativeConstant_le_polynomial_base_eight {T k : ℕ} (hT : 3 ≤ T)
    (hk : k ≤ 8 * T) :
    (Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2 ≤ ((4 * (T : ℝ)) ^ 3) ^ k := by
  have hT' : 3 ≤ (T : ℝ) := by exact_mod_cast hT
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hf : (k.factorial : ℝ) ≤ (8 * (T : ℝ)) ^ k := by
    exact_mod_cast (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hk k)
  calc
    _ ≤ 2 ^ k * ((8 * (T : ℝ)) ^ k) ^ 2 := by gcongr
    _ = (2 * (8 * (T : ℝ)) ^ 2) ^ k := by
      rw [mul_pow 2 ((8 * (T : ℝ)) ^ 2), ← pow_mul, ← pow_mul, Nat.mul_comm k 2]
    _ ≤ ((4 * (T : ℝ)) ^ 3) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      have h := mul_nonneg (show 0 ≤ 64 * (T : ℝ) - 128 by linarith)
        (sq_nonneg (T : ℝ))
      nlinarith

theorem norm_iteratedDeriv_explicitPassingMask_le_polynomial_base_eight {T : ℕ}
    (hT : 3 ≤ T) {k : ℕ} (hk : k ≤ 8 * T) {δ : ℝ} (hδ : 0 < δ)
    (Z : Set ℝ) (x : ℝ) :
    ‖iteratedDeriv k (explicitPassingMask (8 * T) δ Z) x‖ ≤
      ((4 * (T : ℝ)) ^ 3 / δ) ^ k := by
  calc
    _ ≤ δ⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) :=
      norm_iteratedDeriv_explicitPassingMask_le (8 * T) k hk hδ Z x
    _ ≤ δ⁻¹ ^ k * ((4 * (T : ℝ)) ^ 3) ^ k :=
      mul_le_mul_of_nonneg_left
        (explicitDerivativeConstant_le_polynomial_base_eight hT hk) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; simp only [div_eq_mul_inv, mul_comm]

end FalconerThetaGauge
