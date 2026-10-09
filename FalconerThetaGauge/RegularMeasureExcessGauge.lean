/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureExcess

/-!
# The gauge lower bound for the actual excess function

A generation-`n` cube fits in the open ball of radius `2^(-n)` about its
midpoint. The gauge estimate and the retained part's actual mass give the
lower excess barrier with the exact normalization cost.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeLogEnergy GaugeSeparatedMeasures

/-- The geometric midpoint of a half-open dyadic square. -/
def dyadicCubeCenter (n : ℕ) (k : Fin 2 → ℤ) : Plane :=
  WithLp.toLp 2 (fun i ↦ ((k i : ℝ) + 1 / 2) / (2 : ℝ) ^ n)

/-- The half diagonal is strictly smaller than the side length. -/
theorem dyadicCube_subset_ball_center (n : ℕ) (k : Fin 2 → ℤ) :
    dyadicCube n k ⊆ Metric.ball (dyadicCubeCenter n k) (dyadicRadius n) := by
  intro x hx
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hr : 0 < dyadicRadius n := dyadicRadius_pos n
  have hpr : (2 : ℝ) ^ n * dyadicRadius n = 1 := by
    rw [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      mul_inv_cancel₀ hp.ne']
  have hcoord (i : Fin 2) : |(x - dyadicCubeCenter n k) i| ≤ dyadicRadius n / 2 := by
    have hcenter : (2 : ℝ) ^ n * dyadicCubeCenter n k i = (k i : ℝ) + 1 / 2 := by
      change (2 : ℝ) ^ n * (((k i : ℝ) + 1 / 2) / (2 : ℝ) ^ n) = _
      exact mul_div_cancel₀ _ hp.ne'
    have hscaled : |(2 : ℝ) ^ n * (x i - dyadicCubeCenter n k i)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [(hx i).1, (hx i).2]
    rw [abs_mul, abs_of_pos hp] at hscaled
    change |x i - dyadicCubeCenter n k i| ≤ dyadicRadius n / 2
    nlinarith
  have hsq (i : Fin 2) : ((x - dyadicCubeCenter n k) i) ^ 2 ≤ (dyadicRadius n / 2) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hcoord i)
    simpa only [sq_abs] using h
  have hnorm : ‖x - dyadicCubeCenter n k‖ ^ 2 ≤ (dyadicRadius n) ^ 2 / 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith [hsq 0, hsq 1]
  rw [Metric.mem_ball, dist_eq_norm]
  nlinarith [norm_nonneg (x - dyadicCubeCenter n k), sq_pos_of_pos hr]

/-- The dyadic gauge is exactly the power given by the manuscript's profile `g(n)`. -/
theorem realGauge_dyadicRadius_eq_excess (θ : ℝ) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    realGauge θ (dyadicRadius n) = (2 : ℝ) ^ (-(n : ℝ)) *
      (2 : ℝ) ^ (-(N : ℝ) * gaugeExcess θ N n) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [realGauge, log_inv_dyadicRadius]
  change (2 : ℝ) ^ (-(n : ℝ)) * Real.exp (-((n : ℝ) * Real.log 2) ^ θ) = _
  congr 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold gaugeExcess
  field_simp

/-- The actual cube inherits the gauge ball estimate with no geometric constant loss. -/
theorem unitCellWeight_le_gauge_power (μ : Measure Plane) [IsFiniteMeasure μ]
    {θ C : ℝ} (hC : 0 ≤ C) (hball : HasGaugeBallBound μ θ C) {N : ℕ} (hN : 0 < N)
    {n : ℕ} (hn : 1 ≤ n) (k : Fin 2 → ℤ) :
    unitCellWeight μ n k ≤ C * ((2 : ℝ) ^ (-(n : ℝ)) *
      (2 : ℝ) ^ (-(N : ℝ) * gaugeExcess θ N n)) := by
  have hr1 : dyadicRadius n < 1 :=
    (dyadicRadius_le_half hn).trans_lt (by norm_num)
  have hb := (measure_mono (dyadicCube_subset_ball_center n k)).trans
    (hball (dyadicCubeCenter n k) _ (dyadicRadius_pos n) hr1)
  have hprod : ENNReal.ofReal C * ENNReal.ofReal (realGauge θ (dyadicRadius n)) =
      ENNReal.ofReal (C * realGauge θ (dyadicRadius n)) := (ENNReal.ofReal_mul hC).symm
  rw [hprod] at hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hC (realGauge_pos θ (dyadicRadius_pos n)).le),
    realGauge_dyadicRadius_eq_excess θ hN n] at hreal
  exact hreal

/-- Normalizing an actual retained set costs exactly its reciprocal original mass. -/
theorem normalizedRestrict_unitCellWeight_le (μ : Measure Plane) [IsFiniteMeasure μ]
    (G : Set Plane) {τ v : ℝ} (hmass : (2 : ℝ) ^ (-τ) ≤ μ.real G)
    {n : ℕ} {k : Fin 2 → ℤ} (hcell : unitCellWeight μ n k ≤ (2 : ℝ) ^ v) :
    unitCellWeight (normalizedRestrict μ G) n k ≤ (2 : ℝ) ^ (v + τ) := by
  have hinv : (μ.real G)⁻¹ ≤ (2 : ℝ) ^ τ := by
    have h := inv_anti₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hmass
    simpa only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv] using h
  rw [unitCellWeight, Measure.real,
    normalizedRestrict_apply _ _ _ (measurableSet_dyadicCube n k),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  calc
    _ ≤ (2 : ℝ) ^ τ * (2 : ℝ) ^ v :=
      mul_le_mul hinv ((measureReal_mono Set.inter_subset_left).trans hcell)
        measureReal_nonneg (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num), add_comm]

/-- An actual cell power bound gives the actual excess lower barrier. -/
theorem regularMeasureExcess_lower_of_cell_power (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N : ℕ} (hN : 0 < N) (n : ℕ) (g κ : ℝ)
    (hcell : ∀ k ∈ unitCellIndices n,
      unitCellWeight ρ n k ≤ (2 : ℝ) ^ (-(n : ℝ) - (N : ℝ) * (g - κ))) :
    g - κ ≤ regularMeasureExcess ρ N n := by
  obtain ⟨k, hk, hmass⟩ := exists_unitCellWeight_eq_maxCellMass ρ n
  have hmax : maxCellMass ρ n ≤ (2 : ℝ) ^ (-(n : ℝ) - (N : ℝ) * (g - κ)) := by
    rw [hmass]
    exact hcell k hk
  rw [maxCellMass_eq_power_excess ρ hρ hN n, ← Real.rpow_add (by norm_num)] at hmax
  have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hmax
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

/-- The gauge bound and literal part threshold give Lemma 5.10(iii) for `n≥1`. -/
theorem regularMeasureExcess_normalizedRestrict_lower (μ : Measure Plane) [IsFiniteMeasure μ]
    (G : Set Plane) {θ C κ : ℝ} (hC : 0 ≤ C) (hball : HasGaugeBallBound μ θ C)
    {N : ℕ} (hN : 0 < N) (hmass : (2 : ℝ) ^ (-(κ * N / 2)) ≤ μ.real G)
    (hconstant : C ≤ (2 : ℝ) ^ (κ * N / 2))
    [IsProbabilityMeasure (normalizedRestrict μ G)]
    (hρ : normalizedRestrict μ G unitSquare = 1) {n : ℕ} (hn : 1 ≤ n) :
    gaugeExcess θ N n - κ ≤ regularMeasureExcess (normalizedRestrict μ G) N n := by
  apply regularMeasureExcess_lower_of_cell_power _ hρ hN n (gaugeExcess θ N n) κ
  intro k _
  have hcell := (unitCellWeight_le_gauge_power μ hC hball hN hn k).trans
    (mul_le_mul_of_nonneg_right hconstant (by positivity))
  have hcell' : unitCellWeight μ n k ≤
      (2 : ℝ) ^ (κ * N / 2 - (n : ℝ) - (N : ℝ) * gaugeExcess θ N n) := by
    convert hcell using 1
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have h := normalizedRestrict_unitCellWeight_le μ G hmass hcell'
  convert h using 1
  congr 1
  ring

theorem constant_le_power_of_log_budget {C κ : ℝ} (hC : 0 < C) (N : ℕ)
    (hconstant : Real.log C / Real.log 2 ≤ κ * N / 2) :
    C ≤ (2 : ℝ) ^ (κ * N / 2) := by
  apply (Real.log_le_log_iff hC (Real.rpow_pos_of_pos (by norm_num) _)).mp
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hconstant

/-- The lower barrier includes the zero generation, as in Lemma 5.10(iii). -/
theorem regularMeasureExcess_normalizedRestrict_lower_all
    (μ : Measure Plane) [IsFiniteMeasure μ] (G : Set Plane) {θ C κ : ℝ}
    (hθ : 0 < θ) (hC : 0 < C) (hκ : 0 ≤ κ) (hball : HasGaugeBallBound μ θ C)
    {N : ℕ} (hN : 0 < N) (hmass : (2 : ℝ) ^ (-(κ * N / 2)) ≤ μ.real G)
    (hconstant : Real.log C / Real.log 2 ≤ κ * N / 2)
    [IsProbabilityMeasure (normalizedRestrict μ G)]
    (hρ : normalizedRestrict μ G unitSquare = 1) (n : ℕ) :
    gaugeExcess θ N n - κ ≤ regularMeasureExcess (normalizedRestrict μ G) N n := by
  by_cases hn : n = 0
  · subst n
    simp only [gaugeExcess, Nat.cast_zero, zero_mul, Real.zero_rpow hθ.ne', zero_div,
      regularMeasureExcess_zero _ hρ N, zero_sub]
    exact neg_nonpos.mpr hκ
  · exact regularMeasureExcess_normalizedRestrict_lower μ G hC.le hball hN hmass
      (constant_le_power_of_log_budget hC N hconstant) hρ (by omega)

theorem gaugeExcess_nonneg (θ : ℝ) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    0 ≤ gaugeExcess θ N n := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold gaugeExcess
  positivity

/-- All four conclusions of Lemma 5.10 for an actual normalized retained part. -/
theorem regularMeasureExcess_normalizedRestrict_properties
    (μ : Measure Plane) [IsFiniteMeasure μ] (G : Set Plane) {θ C κ : ℝ}
    (hθ : 0 < θ) (hC : 0 < C) (hκ : 0 ≤ κ) (hball : HasGaugeBallBound μ θ C)
    {N : ℕ} (hN : 0 < N) (hmass : (2 : ℝ) ^ (-(κ * N / 2)) ≤ μ.real G)
    (hconstant : Real.log C / Real.log 2 ≤ κ * N / 2)
    [IsProbabilityMeasure (normalizedRestrict μ G)]
    (hρ : normalizedRestrict μ G unitSquare = 1) :
    regularMeasureExcess (normalizedRestrict μ G) N 0 = 0 ∧
      (∀ n m : ℕ, |regularMeasureExcess (normalizedRestrict μ G) N n -
        regularMeasureExcess (normalizedRestrict μ G) N m| ≤ |(n : ℝ) - m| / N) ∧
      (∀ n : ℕ, gaugeExcess θ N n - κ ≤
        regularMeasureExcess (normalizedRestrict μ G) N n) ∧
      (∀ n : ℕ, regularMeasureExcess (normalizedRestrict μ G) N n ≤ (n : ℝ) / N) :=
  ⟨regularMeasureExcess_zero _ hρ N,
    regularMeasureExcess_lipschitz _ hρ hN,
    regularMeasureExcess_normalizedRestrict_lower_all μ G hθ hC hκ hball hN hmass hconstant hρ,
    regularMeasureExcess_le_generation _ hρ hN⟩

end FalconerThetaGauge
