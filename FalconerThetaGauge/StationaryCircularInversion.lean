module

public import FalconerThetaGauge.StationaryCircularPreparedExpansion
public import FalconerThetaGauge.StationaryCircularPeriodic
public import FalconerThetaGauge.StationaryPhaseFiniteTailBudget
public import FalconerThetaGauge.StationaryPhaseInverseOperatorsRegularityBudget

/-! # Actual prepared circular integrals and exact finite stationary inversion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset Function
open scoped ContDiff

namespace FalconerThetaGauge

def preparedCirclePhaseFactor (Λ : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi / Λ) : ℂ) *
    Complex.exp (-((Λ - Real.pi / 4 : ℝ) : ℂ) * Complex.I)

def preparedInverseCircleIntegral (T : ℕ) (α : ℝ) (B : ℝ → ℂ)
    (φ Λ u : ℝ) (j : ℕ) : ℂ :=
  ∫ t in u..u + 2 * Real.pi,
    Complex.exp (-((Λ * Real.cos (t - φ) : ℝ) : ℂ) * Complex.I) *
      preparedAngularAmplitude (6 * T) α (stationaryPhaseInverseOperator j B) t

def preparedInverseCircleSeries (T : ℕ) (α : ℝ) (B : ℝ → ℂ) (φ Λ u : ℝ) : ℂ :=
  ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * preparedInverseCircleIntegral T α B φ Λ u j

def preparedInverseCircleError (T : ℕ) (α : ℝ) (B : ℝ → ℂ)
    (φ Λ u : ℝ) (j : ℕ) : ℂ :=
  preparedInverseCircleIntegral T α B φ Λ u j - preparedCirclePhaseFactor Λ *
    ∑ i ∈ range T, (Λ : ℂ)⁻¹ ^ i *
      stationaryPhaseOperator i (stationaryPhaseInverseOperator j B) φ

theorem norm_preparedCirclePhaseFactor (Λ : ℝ) :
    ‖preparedCirclePhaseFactor Λ‖ = Real.sqrt (2 * Real.pi / Λ) := by
  simp [preparedCirclePhaseFactor, Complex.norm_exp,
    Complex.mul_re, Real.sqrt_nonneg]

theorem stationaryPhaseFiniteProduct_eq_iterated_sum (T : ℕ) (z : ℂ)
    (B : ℝ → ℂ) (φ : ℝ) :
    stationaryPhaseFiniteProduct T z B φ =
      ∑ j ∈ range T, z ^ j * ∑ i ∈ range T,
        z ^ i * stationaryPhaseOperator i (stationaryPhaseInverseOperator j B) φ := by
  rw [stationaryPhaseFiniteProduct, Finset.product_eq_sprod]
  rw [Finset.sum_product' (range T) (range T)
    (fun i j ↦ z ^ i * z ^ j *
      stationaryPhaseOperator i (stationaryPhaseInverseOperator j B) φ), sum_comm]
  simp only [mul_sum]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro i hi
  ring

/-- The actual inverse integrals have exactly the genuine operator tail and their
actual stationary-phase errors; neither remainder is supplied as a hypothesis. -/
theorem preparedInverseCircleSeries_sub_eq {T : ℕ} (hT : 0 < T)
    (α : ℝ) {B : ℝ → ℂ} (hB : ContDiff ℝ ∞ B) (φ Λ u : ℝ) :
    preparedInverseCircleSeries T α B φ Λ u - preparedCirclePhaseFactor Λ * B φ =
      preparedCirclePhaseFactor Λ * stationaryPhaseFiniteTail T (Λ : ℂ)⁻¹ B φ +
        ∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j * preparedInverseCircleError T α B φ Λ u j := by
  have hs := stationaryPhaseFiniteProduct_eq_add_tail hB hT (Λ : ℂ)⁻¹ φ
  rw [stationaryPhaseFiniteProduct_eq_iterated_sum] at hs
  rw [preparedInverseCircleSeries]
  simp only [preparedInverseCircleError, mul_sub, sum_sub_distrib]
  have he : (∑ j ∈ range T, (Λ : ℂ)⁻¹ ^ j *
      (preparedCirclePhaseFactor Λ * ∑ i ∈ range T, (Λ : ℂ)⁻¹ ^ i *
        stationaryPhaseOperator i (stationaryPhaseInverseOperator j B) φ)) =
      preparedCirclePhaseFactor Λ * (B φ + stationaryPhaseFiniteTail T (Λ : ℂ)⁻¹ B φ) := by
    rw [← hs, mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [he]
  ring

theorem norm_preparedInverseCircleError_le {T : ℕ} (hT : 1 ≤ T)
    {B : ℝ → ℂ} {A M α φ Λ : ℝ} (hB : IsDerivativeRegular A M (6 * T) B)
    (hBs : ContDiff ℝ ∞ B) (hBP : Periodic B (2 * Real.pi)) (hΛ : 1 ≤ Λ)
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) (u : ℝ)
    {j : ℕ} (hj : j ∈ range T) :
    ‖preparedInverseCircleError T α B φ Λ u j‖ ≤
      (A * (200 * T * M ^ 2) ^ j) * Real.sqrt (2 * Real.pi / Λ) *
        circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) *
          (circularStationaryRemainderBase T (1200 * (T : ℝ) ^ 2 + M) / Λ) ^ T := by
  have hjT := mem_range.mp hj
  have hreg := stationaryPhaseInverseOperator_isDerivativeRegular_uniform
    (hB.of_le (by omega : 4 * T + 2 * j ≤ 6 * T)) T (le_of_lt hjT)
  have h := circular_stationary_phase_prepared_arc hT hreg
    (contDiff_stationaryPhaseInverseOperator hBs j)
    (periodic_stationaryPhaseInverseOperator hBP j) hΛ hφ u
  simpa only [preparedInverseCircleError, preparedInverseCircleIntegral,
    preparedCirclePhaseFactor, mul_assoc] using h

end FalconerThetaGauge
