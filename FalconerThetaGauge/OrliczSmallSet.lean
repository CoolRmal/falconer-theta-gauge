module

public import FalconerThetaGauge.RadialProjectionUniformIntegrability
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Quantitative small-set mass bounds for the actual Orlicz density

These are the density estimates in the removed-mass argument (Lemma 6.13).
They retain the exact threshold, the true reference measure of the bad-direction
set, and the literal logarithmic Orlicz integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

theorem orliczTailCoefficient_le_log {γ H : ℝ} (hγ : 0 ≤ γ) (hH : 1 < H) :
    orliczTailCoefficient γ H ≤ ENNReal.ofReal ((Real.log H) ^ (-γ)) := by
  have hlog : 0 < Real.log H := Real.log_pos hH
  have hpow : (Real.log H) ^ γ ≤ (Real.log (Real.exp 1 + H)) ^ γ := by
    apply Real.rpow_le_rpow hlog.le _ hγ
    exact Real.log_le_log (zero_lt_one.trans hH)
      (le_add_of_nonneg_left (Real.exp_nonneg 1))
  rw [orliczTailCoefficient, Real.rpow_neg hlog.le,
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hlog γ)]
  exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hpow)

/-- A bad-direction set of arc length `δ` carries at most `Hδ + K(log H)^(-γ)` mass. -/
theorem withDensity_small_set_orlicz {α : Type*} [MeasurableSpace α]
    (ξ : Measure α) {f : α → ℝ≥0∞} {γ H : ℝ} (hγ : 0 ≤ γ) (hH : 1 < H)
    {K : ℝ≥0∞} (hK : (∫⁻ x, orliczPhiExtended γ (f x) ∂ξ) ≤ K)
    {Z : Set α} (hZ : MeasurableSet Z) :
    ξ.withDensity f Z ≤ ENNReal.ofReal H * ξ Z +
      ENNReal.ofReal ((Real.log H) ^ (-γ)) * K :=
  (withDensity_le_cutoff_add_orlicz ξ hγ (zero_lt_one.trans hH) hK hZ).trans
    (add_le_add le_rfl (mul_le_mul' (orliczTailCoefficient_le_log hγ hH) le_rfl))

theorem log_inverse_eighth_le {E H : ℝ} (hE : 0 < E)
    (hlog : E / 2 ≤ Real.log H) :
    (Real.log H) ^ (-8 : ℝ) ≤ (2 : ℝ) ^ 8 * E ^ (-8 : ℝ) := by
  have hpow : (Real.log H) ^ (-8 : ℝ) ≤ (E / 2) ^ (-8 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hlog (by norm_num)
  calc
    _ ≤ (E / 2) ^ (-8 : ℝ) := hpow
    _ = _ := by
      rw [Real.div_rpow hE.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul]
      norm_num
      ring

/-- The exact eighth-order tail cost used by the scale-dependent filter. -/
theorem withDensity_filter_cutoff {α : Type*} [MeasurableSpace α]
    (ξ : Measure α) {f : α → ℝ≥0∞} {E H A : ℝ}
    (hE : 0 < E) (hH : 1 < H) (hlog : E / 2 ≤ Real.log H)
    {K : ℝ≥0∞} (hK : (∫⁻ x, orliczPhiExtended 8 (f x) ∂ξ) ≤ K)
    {Z : Set α} (hZ : MeasurableSet Z) (hshort : ENNReal.ofReal H * ξ Z ≤ ENNReal.ofReal A) :
    ξ.withDensity f Z ≤ ENNReal.ofReal A +
      ENNReal.ofReal ((2 : ℝ) ^ 8 * E ^ (-8 : ℝ)) * K :=
  (withDensity_small_set_orlicz ξ (by norm_num) hH hK hZ).trans
    (add_le_add hshort (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (log_inverse_eighth_le hE hlog)) le_rfl))

/-- The actual maximum arc length of the union of at most `N²+1` failed tests. -/
def filterBadDirectionLength (N : ℕ) (E : ℝ) : ℝ :=
  2 * Real.pi * ((N : ℝ) ^ 2 + 1) * (2 : ℝ) ^ (-2 * E)

/-- The filter uses the reciprocal square root of its explicit arc-length bound. -/
def filterOrliczThreshold (N : ℕ) (E : ℝ) : ℝ :=
  filterBadDirectionLength N E ^ (-(1 / 2 : ℝ))

theorem filterBadDirectionLength_pos (N : ℕ) (E : ℝ) :
    0 < filterBadDirectionLength N E := by
  unfold filterBadDirectionLength
  positivity

theorem filterOrliczThreshold_pos (N : ℕ) (E : ℝ) :
    0 < filterOrliczThreshold N E :=
  Real.rpow_pos_of_pos (filterBadDirectionLength_pos N E) _

theorem log_filterOrliczThreshold (N : ℕ) (E : ℝ) :
    Real.log (filterOrliczThreshold N E) =
      E * Real.log 2 - Real.log (2 * Real.pi * ((N : ℝ) ^ 2 + 1)) / 2 := by
  rw [filterOrliczThreshold, Real.log_rpow (filterBadDirectionLength_pos N E)]
  unfold filterBadDirectionLength
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num)]
  ring

theorem filterOrliczThreshold_log_lower (N : ℕ) {E : ℝ}
    (hbudget : Real.log (2 * Real.pi * ((N : ℝ) ^ 2 + 1)) ≤ (2 * Real.log 2 - 1) * E) :
    E / 2 ≤ Real.log (filterOrliczThreshold N E) := by
  rw [log_filterOrliczThreshold]
  nlinarith

theorem filterOrliczThreshold_mul_length_le (N : ℕ) (E : ℝ) :
    filterOrliczThreshold N E * filterBadDirectionLength N E ≤
      3 * (N + 1 : ℝ) * (2 : ℝ) ^ (-E) := by
  let B := filterBadDirectionLength N E
  let A : ℝ := 3 * (N + 1 : ℝ) * (2 : ℝ) ^ (-E)
  have hB : 0 < B := filterBadDirectionLength_pos N E
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoef : 2 * Real.pi * ((N : ℝ) ^ 2 + 1) ≤ 9 * (N + 1 : ℝ) ^ 2 := by
    have hπ := Real.pi_lt_four
    have hN := Nat.cast_nonneg (α := ℝ) N
    nlinarith [sq_nonneg (N : ℝ), mul_le_mul_of_nonneg_right hπ.le
      (show 0 ≤ (N : ℝ) ^ 2 + 1 by positivity)]
  have hAsq : A ^ 2 = 9 * (N + 1 : ℝ) ^ 2 * (2 : ℝ) ^ (-2 * E) := by
    dsimp [A]
    rw [mul_pow, mul_pow]
    have hf : ((2 : ℝ) ^ (-E)) ^ (2 : ℕ) = (2 : ℝ) ^ (-2 * E) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hf]
    norm_num
  have hBA : B ≤ A ^ 2 := by
    rw [hAsq]
    exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by norm_num) _)
  have hroot := Real.rpow_le_rpow hB.le hBA (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hrootA : (A ^ 2) ^ (1 / 2 : ℝ) = A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  rw [hrootA] at hroot
  have hHB : filterOrliczThreshold N E * B = B ^ (1 / 2 : ℝ) := by
    change B ^ (-(1 / 2 : ℝ)) * B = _
    conv_lhs => rhs; rw [← Real.rpow_one B]
    rw [← Real.rpow_add hB]
    norm_num
  exact hHB.trans_le hroot

/-- The exact small-bad-direction bound in Lemma 6.13, with `E=εN`. -/
theorem withDensity_filter_bad_directions {α : Type*} [MeasurableSpace α]
    (ξ : Measure α) {f : α → ℝ≥0∞} (N : ℕ) {E : ℝ} (hE : 0 < E)
    (hH : 1 < filterOrliczThreshold N E)
    (hlog : E / 2 ≤ Real.log (filterOrliczThreshold N E))
    {K : ℝ≥0∞} (hK : (∫⁻ x, orliczPhiExtended 8 (f x) ∂ξ) ≤ K)
    {Z : Set α} (hZ : MeasurableSet Z)
    (hlength : ξ Z ≤ ENNReal.ofReal (filterBadDirectionLength N E)) :
    ξ.withDensity f Z ≤ ENNReal.ofReal (3 * (N + 1 : ℝ) * (2 : ℝ) ^ (-E)) +
      ENNReal.ofReal ((2 : ℝ) ^ 8 * E ^ (-8 : ℝ)) * K := by
  apply withDensity_filter_cutoff ξ hE hH hlog hK hZ
  calc
    _ ≤ ENNReal.ofReal (filterOrliczThreshold N E) *
        ENNReal.ofReal (filterBadDirectionLength N E) := mul_le_mul' le_rfl hlength
    _ = ENNReal.ofReal (filterOrliczThreshold N E * filterBadDirectionLength N E) :=
      (ENNReal.ofReal_mul (filterOrliczThreshold_pos N E).le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (filterOrliczThreshold_mul_length_le N E)

/-- The explicit scalar budget proves the threshold and removes both auxiliary
threshold assumptions from the final short-direction-set estimate. -/
theorem withDensity_filter_bad_directions_of_budget {α : Type*} [MeasurableSpace α]
    (ξ : Measure α) {f : α → ℝ≥0∞} (N : ℕ) {E : ℝ} (hE : 0 < E)
    (hbudget : Real.log (2 * Real.pi * ((N : ℝ) ^ 2 + 1)) ≤ (2 * Real.log 2 - 1) * E)
    {K : ℝ≥0∞} (hK : (∫⁻ x, orliczPhiExtended 8 (f x) ∂ξ) ≤ K)
    {Z : Set α} (hZ : MeasurableSet Z)
    (hlength : ξ Z ≤ ENNReal.ofReal (filterBadDirectionLength N E)) :
    ξ.withDensity f Z ≤ ENNReal.ofReal (3 * (N + 1 : ℝ) * (2 : ℝ) ^ (-E)) +
      ENNReal.ofReal ((2 : ℝ) ^ 8 * E ^ (-8 : ℝ)) * K := by
  have hlog := filterOrliczThreshold_log_lower N hbudget
  have hH : 1 < filterOrliczThreshold N E := by
    have hlogpos : 0 < Real.log (filterOrliczThreshold N E) := (by positivity : (0 : ℝ) < E / 2).trans_le hlog
    have h := Real.exp_lt_exp.mpr hlogpos
    rwa [Real.exp_zero, Real.exp_log (filterOrliczThreshold_pos N E)] at h
  exact withDensity_filter_bad_directions ξ N hE hH hlog hK hZ hlength

end FalconerThetaGauge
