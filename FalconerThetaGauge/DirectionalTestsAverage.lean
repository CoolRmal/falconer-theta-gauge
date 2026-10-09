module

public import FalconerThetaGauge.DirectionalTestsAverageTubeBound
public import FalconerThetaGauge.DirectionalTestsMaskSupport

/-! # Lemma 6.5 with the actual scale-dependent parameter facts -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The actual (P1) budget absorbs both explicit average-count polynomial factors. -/
theorem ParameterFacts.directional_average_budgets {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    150 * ((N : ℝ) + 4) ≤ (2 : ℝ) ^ (tolerance θ N * N) ∧
      75 * ((N : ℝ) + 2) ≤ (2 : ℝ) ^ (tolerance θ N * N) := by
  have hT : 1 ≤ ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (expansionCount θ N)])
  have hcoef : (150 : ℝ) ≤ (2 : ℝ) ^ (80 : ℕ) *
      ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) := by
    have hsmall : (150 : ℝ) ≤ (2 : ℝ) ^ (80 : ℕ) := by norm_num
    have h := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ (2 : ℝ) ^ (80 : ℕ))
    exact hsmall.trans (by simpa only [mul_one] using h)
  have hbase : 1 ≤ (N : ℝ) + 16 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpow : (N : ℝ) + 16 ≤ ((N : ℝ) + 16) ^ (12 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by norm_num : (1 : ℕ) ≤ 12)
  have hpoly : 150 * ((N : ℝ) + 4) ≤ (2 : ℝ) ^ (80 : ℕ) *
      ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) * ((N : ℝ) + 16) ^ (12 : ℕ) :=
    mul_le_mul hcoef (by linarith) (by positivity) (by positivity)
  have hE : 0 ≤ tolerance θ N * N := le_trans (by norm_num) hpar.2.2.1.1
  have hpower : (2 : ℝ) ^ (tolerance θ N * N / 8) ≤
      (2 : ℝ) ^ (tolerance θ N * N) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h := hpoly.trans (hpar.2.1.trans hpower)
  refine ⟨h, ?_⟩
  exact (show 75 * ((N : ℝ) + 2) ≤ 150 * ((N : ℝ) + 4) by
    linarith [Nat.cast_nonneg (α := ℝ) N]).trans h

/-- The actual equally spaced mask levels meet the exact source width-gap requirement. -/
theorem ParameterFacts.directional_level_size {θ : ℝ} {N : ℕ} (hpar : ParameterFacts θ N) :
    (maskLevelCount θ N : ℝ) ≤ (2 : ℝ) ^ (tolerance θ N * N) / 8 := by
  have hI : (maskLevelCount θ N : ℝ) ≤ expansionCount θ N := by
    exact_mod_cast hpar.2.2.2.2.2.2.2.2.2.2.1
  have hT : (expansionCount θ N : ℝ) ≤ ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) := by
    have hbase : 1 ≤ (expansionCount θ N : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (expansionCount θ N)]
    have hpow : (expansionCount θ N : ℝ) + 1 ≤ ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase (by norm_num : (1 : ℕ) ≤ 12)
    linarith
  have hcoef : (8 : ℝ) ≤ (2 : ℝ) ^ (80 : ℕ) * ((N : ℝ) + 16) ^ (12 : ℕ) := by
    have hpow : 1 ≤ ((N : ℝ) + 16) ^ (12 : ℕ) :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
    have h := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (2 : ℝ) ^ (80 : ℕ))
    have hsmall : (8 : ℝ) ≤ (2 : ℝ) ^ (80 : ℕ) := by norm_num
    exact hsmall.trans (by simpa only [mul_one] using h)
  have hpoly : 8 * (maskLevelCount θ N : ℝ) ≤ (2 : ℝ) ^ (80 : ℕ) *
      ((expansionCount θ N : ℝ) + 1) ^ (12 : ℕ) * ((N : ℝ) + 16) ^ (12 : ℕ) := by
    have h := mul_le_mul hcoef (hI.trans hT) (Nat.cast_nonneg _) (by positivity)
    convert h using 1
    ring
  have hE : 0 ≤ tolerance θ N * N := le_trans (by norm_num) hpar.2.2.1.1
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  have hpower : (2 : ℝ) ^ (tolerance θ N * N / 8) ≤
      (2 : ℝ) ^ (tolerance θ N * N) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h := hpoly.trans (hpar.2.1.trans hpower)
  simpa only [mul_comm] using h

/-- Lemma 6.5 for the genuine tube test at the actual scale-dependent tolerance. -/
theorem tubeAverage_le_height_of_parameterFacts (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N g p : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ) (hgp : g ≤ p) (hp : p ≤ N) (P : Fin 2 → ℤ) :
    tubeAverage ρ g p (tolerance θ N * N) P ≤
      (2 : ℝ) ^ ((N : ℝ) *
        (profileHeight (regularMeasureExcess ρ N) p g p + 4 * tolerance θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  exact tubeAverage_le_height ρ hρ (tolerance_pos θ hN).le hN hreg hgp hp P
    hpar.directional_average_budgets.1

/-- Lemma 6.5 for the genuine normalized-anchor projection test at the actual tolerance. -/
theorem projectionAverage_le_height_of_parameterFacts (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N p u : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (hpu : p ≤ u) (hu : u ≤ N) (P : Fin 2 → ℤ) (hP : 0 < unitCellWeight ρ p P) :
    projectionAverage ρ p u (tolerance θ N * N) P ≤
      (2 : ℝ) ^ (-((u : ℝ) - p)) * (2 : ℝ) ^ ((N : ℝ) *
        (profileHeight (regularMeasureExcess ρ N) p p u + 4 * tolerance θ N)) := by
  have hN : 0 < N := by have := hpar.1; omega
  exact projectionAverage_le_height ρ hρ (tolerance_pos θ hN).le hN hreg hpu hu P hP
    hpar.directional_average_budgets.2

end FalconerThetaGauge
