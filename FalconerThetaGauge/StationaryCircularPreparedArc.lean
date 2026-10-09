module

public import FalconerThetaGauge.StationaryCircularSource
public import FalconerThetaGauge.SeparatedDirectionsCutoff

/-! # The actual one-sided expansion localized to the prepared direction arc -/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset Function Filter
open scoped ContDiff Topology

namespace FalconerThetaGauge

/-- The actual source `ψ`, as a complex periodic angular function. -/
def preparedAngularCutoff (K : ℕ) (α : ℝ) : ℝ → ℂ :=
  fun φ ↦ (preparedArcCutoff K α (unitCircleOfAngle φ) : ℂ)

/-- Multiplication by the actual localized source cutoff. -/
def preparedAngularAmplitude (K : ℕ) (α : ℝ) (H : ℝ → ℂ) : ℝ → ℂ :=
  preparedAngularCutoff K α * H

theorem contDiff_preparedAngularCutoff (K : ℕ) (α : ℝ) :
    ContDiff ℝ ∞ (preparedAngularCutoff K α) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_preparedArcCutoff_comp_angle K α)

theorem periodic_preparedAngularCutoff (K : ℕ) (α : ℝ) :
    Periodic (preparedAngularCutoff K α) (2 * Real.pi) := by
  intro φ
  simp only [preparedAngularCutoff, unitCircleOfAngle_add_two_pi]

/-- The literal source cutoff is `(1,1200T²)`-regular through `6T`. -/
theorem preparedAngularCutoff_isDerivativeRegular {T : ℕ} (hT : 1 ≤ T) (α : ℝ) :
    IsDerivativeRegular 1 (1200 * (T : ℝ) ^ 2) (6 * T) (preparedAngularCutoff (6 * T) α) := by
  have hT' : 1 ≤ (T : ℝ) := by exact_mod_cast hT
  have hscale : 1 ≤ 1200 * (T : ℝ) ^ 2 := by nlinarith
  refine ⟨by norm_num, hscale, (contDiff_preparedAngularCutoff _ _).of_le (by
    exact WithTop.coe_le_coe.mpr (le_top : ((6 * T : ℕ) : ℕ∞) ≤ ⊤)), ?_⟩
  intro k hk φ
  change ‖iteratedDeriv k
    (fun t ↦ (preparedArcCutoff (6 * T) α (unitCircleOfAngle t) : ℂ)) φ‖ ≤ _
  rw [iteratedDeriv_ofReal_function
    ((contDiff_preparedArcCutoff_comp_angle (6 * T) α).of_le (by simp)).contDiffAt,
    Complex.norm_real]
  have hfact := factorial_cast_le_cutoff_order_pow hk
  calc
    _ ≤ (33 : ℝ) ^ k * (k.factorial : ℝ) ^ 2 :=
      norm_iteratedDeriv_preparedArcCutoff_le (6 * T) k hk α φ
    _ ≤ (33 : ℝ) ^ k * ((6 * (T : ℝ)) ^ k) ^ 2 := by gcongr
    _ = (33 * (6 * (T : ℝ)) ^ 2) ^ k := by
      have hp : ((6 * (T : ℝ)) ^ k) ^ 2 = ((6 * (T : ℝ)) ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      rw [hp, ← mul_pow]
    _ ≤ 1 * (1200 * (T : ℝ) ^ 2) ^ k := by
      simp only [one_mul]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [sq_nonneg (T : ℝ)]

/-- Every actual point of the short arc has a real neighborhood on which `ψ=1`. -/
theorem preparedAngularCutoff_eq_one_near_arc (K : ℕ) (α : ℝ) {φ : ℝ}
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) :
    preparedAngularCutoff K α =ᶠ[𝓝 φ] (fun _ ↦ (1 : ℂ)) := by
  filter_upwards [Metric.ball_mem_nhds φ (by norm_num : (0 : ℝ) < 1 / 10)] with t ht
  have hmem : unitCircleOfAngle t ∈ closedArcNeighborhood (1 / 10)
      (closedDirectionArc α (1 / 40)) := by
    refine ⟨t, Metric.mem_cthickening_of_dist_le t φ (1 / 10) _ hφ ?_, rfl⟩
    exact (Metric.mem_ball.mp ht).le
  simp only [preparedAngularCutoff, preparedArcCutoff_eq_one K α hmem, Complex.ofReal_one]

theorem preparedAngularAmplitude_eq_near_arc (K : ℕ) (α : ℝ) (H : ℝ → ℂ) {φ : ℝ}
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) :
    preparedAngularAmplitude K α H =ᶠ[𝓝 φ] H := by
  filter_upwards [preparedAngularCutoff_eq_one_near_arc K α hφ] with t ht
  simp only [preparedAngularAmplitude, Pi.mul_apply, ht, one_mul]

/-- The amplitude is identically zero near the opposite of every actual direction
in the prepared arc, independently of its other factor. -/
theorem preparedAngularAmplitude_eq_zero_near_opposite (K : ℕ) (α : ℝ)
    (H : ℝ → ℂ) {φ : ℝ} (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) :
    preparedAngularAmplitude K α H =ᶠ[𝓝 (φ + Real.pi)] (fun _ ↦ (0 : ℂ)) := by
  have hop : unitCircleOfAngle (φ + Real.pi) ∈ circleAntipode ''
      closedDirectionArc α (1 / 40) :=
    ⟨unitCircleOfAngle φ, hφ, (unitCircleOfAngle_add_pi φ).symm⟩
  filter_upwards [Metric.ball_mem_nhds (φ + Real.pi)
    (by positivity : (0 : ℝ) < Real.pi / 3)] with t ht
  have hmem : unitCircleOfAngle t ∈ closedArcNeighborhood (Real.pi / 3)
      (circleAntipode '' closedDirectionArc α (1 / 40)) := by
    refine ⟨t, Metric.mem_cthickening_of_dist_le t (φ + Real.pi) _ _ hop ?_, rfl⟩
    exact (Metric.mem_ball.mp ht).le
  simp only [preparedAngularAmplitude, Pi.mul_apply, preparedAngularCutoff,
    preparedArcCutoff_eq_zero_on_opposite K α hmem, Complex.ofReal_zero, zero_mul]

theorem stationaryPhaseOperator_preparedAngularAmplitude (K j : ℕ) (α : ℝ)
    (H : ℝ → ℂ) {φ : ℝ} (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) :
    stationaryPhaseOperator j (preparedAngularAmplitude K α H) φ =
      stationaryPhaseOperator j H φ := by
  apply sum_congr rfl
  intro k _
  rw [(preparedAngularAmplitude_eq_near_arc K α H hφ).iteratedDeriv_eq k]

theorem stationaryPhaseConjugateOperator_preparedAngularAmplitude_eq_zero (K j : ℕ)
    (α : ℝ) (H : ℝ → ℂ) {φ : ℝ}
    (hφ : unitCircleOfAngle φ ∈ closedDirectionArc α (1 / 40)) :
    stationaryPhaseConjugateOperator j (preparedAngularAmplitude K α H) (φ + Real.pi) = 0 := by
  apply sum_eq_zero
  intro k _
  rw [(preparedAngularAmplitude_eq_zero_near_opposite K α H hφ).iteratedDeriv_eq k,
    iteratedDeriv_fun_const_zero, mul_zero]

end FalconerThetaGauge
