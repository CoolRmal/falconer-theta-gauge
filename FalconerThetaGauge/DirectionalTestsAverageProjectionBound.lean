module

public import FalconerThetaGauge.DirectionalTestsAveragePairMass

/-! # The genuine quantitative projection-average half of Lemma 6.5 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- Cancellation of the true angular shell coefficient with the true regular pair mass. -/
theorem projection_shell_coefficient (p u d N : ℕ) (E H : ℝ) :
    (2 * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (d + 1)) *
      (9 * (2 : ℝ) ^ E * (2 : ℝ) ^ (-((d : ℝ) - p)) * (2 : ℝ) ^ ((N : ℝ) * H)) =
      36 * ((2 : ℝ) ^ (3 * E) * (2 : ℝ) ^ ((p : ℝ) - u) * (2 : ℝ) ^ ((N : ℝ) * H)) := by
  have hpow : (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (d : ℝ) *
      (2 : ℝ) ^ E * (2 : ℝ) ^ (-((d : ℝ) - p)) =
      (2 : ℝ) ^ (3 * E) * (2 : ℝ) ^ ((p : ℝ) - u) := by
    simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [pow_succ]
  calc
    _ = 36 * ((2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E) *
        (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ E * (2 : ℝ) ^ (-((d : ℝ) - p))) *
          (2 : ℝ) ^ ((N : ℝ) * H) := by rw [Real.rpow_natCast]; ring
    _ = _ := by rw [hpow]; ring

/-- The actual projection test's average, before absorbing the explicit polynomial constant. -/
theorem projectionAverage_le_explicit_height (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} (hε : 0 ≤ ε) {N p u : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hpu : p ≤ u) (hu : u ≤ N) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) :
    projectionAverage ρ p u (ε * N) P ≤
      75 * ((N : ℝ) + 2) * (2 : ℝ) ^ (3 * (ε * N)) * (2 : ℝ) ^ (-((u : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * profileHeight (regularMeasureExcess ρ N) p p u) := by
  have hprob := isProbabilityMeasure_projectionAnchorMeasure ρ p P hP
  let ν := projectionAnchorMeasure ρ p P
  let E : ℝ := ε * N
  let H : ℝ := profileHeight (regularMeasureExcess ρ N) p p u
  let B : ℝ := (2 : ℝ) ^ (3 * E) * (2 : ℝ) ^ ((p : ℝ) - u) * (2 : ℝ) ^ ((N : ℝ) * H)
  let η : ℝ := 2 * (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (2 * E)
  have hE : 0 ≤ E := mul_nonneg hε (Nat.cast_nonneg N)
  have hH : 0 ≤ H := profileHeight_nonneg le_rfl hpu
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpair (d : ℕ) (hdp : p ≤ d) (hdu : d ≤ u) :
      (ν.prod ν).real (dyadicPairBall d) ≤
      9 * (2 : ℝ) ^ E * (2 : ℝ) ^ (-((d : ℝ) - p)) * (2 : ℝ) ^ ((N : ℝ) * H) :=
    real_projectionAnchor_dyadicPairBall_le_height ρ hρ hN hreg (hpu.trans hu) P hP hdp hdu
  have hsmall : (ν.prod ν).real (dyadicPairBall u) ≤ 9 * B := by
    apply (hpair u hpu le_rfl).trans
    have hpows : (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (3 * E) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpows (by norm_num : (0 : ℝ) ≤ 9))
      (by positivity : 0 ≤ (2 : ℝ) ^ (-((u : ℝ) - p)) * (2 : ℝ) ^ ((N : ℝ) * H))
    rw [show -((u : ℝ) - p) = (p : ℝ) - u by ring] at h
    rw [show -((u : ℝ) - p) = (p : ℝ) - u by ring]
    simpa only [B, mul_assoc] using h
  have hterm (d : ℕ) (hd : d ∈ Finset.Ico p u) :
      (η * (2 : ℝ) ^ (d + 1)) * (ν.prod ν).real (dyadicPairBall d) ≤ 36 * B := by
    have h := mul_le_mul_of_nonneg_left
      (hpair d (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd).2.le)
      (by dsimp [η]; positivity : 0 ≤ η * (2 : ℝ) ^ (d + 1))
    exact h.trans_eq (projection_shell_coefficient p u d N E H)
  have hsum : (∑ d ∈ Finset.Ico p u, (η * (2 : ℝ) ^ (d + 1)) *
      (ν.prod ν).real (dyadicPairBall d)) ≤ (N : ℝ) * (36 * B) := by
    calc
      _ ≤ ∑ _d ∈ Finset.Ico p u, 36 * B := Finset.sum_le_sum hterm
      _ = ((u - p : ℕ) : ℝ) * (36 * B) := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show u - p ≤ N by omega))
        (mul_nonneg (by norm_num) hB)
  have hcoarse : η * (2 : ℝ) ^ p ≤ 2 * B := by
    have hpow : (2 : ℝ) ^ (2 * E) ≤ (2 : ℝ) ^ (3 * E) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hheight : 1 ≤ (2 : ℝ) ^ ((N : ℝ) * H) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg N) hH)
    have heq : η * (2 : ℝ) ^ p = 2 * (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ ((p : ℝ) - u) := by
      have hpowers : (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (p : ℝ) =
          (2 : ℝ) ^ ((p : ℝ) - u) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      dsimp [η]
      rw [← Real.rpow_natCast (2 : ℝ) p]
      calc
        _ = 2 * (2 : ℝ) ^ (2 * E) * ((2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (p : ℝ)) := by ring
        _ = _ := by rw [hpowers]
    rw [heq]
    calc
      _ ≤ 2 * (2 : ℝ) ^ (3 * E) * (2 : ℝ) ^ ((p : ℝ) - u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hheight
          (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (3 * E) * (2 : ℝ) ^ ((p : ℝ) - u))
        simpa only [B, mul_one, mul_assoc] using h
  have hcollision := integral_angularCollisionMajorant_le_dyadic_shells ν
    (by dsimp [η]; positivity : 0 ≤ η) hpu
  have hproj := directionalAverage_projectionCount_le_collision ν u E (by norm_num : (0 : ℝ) ≤ 2)
  have htotal : projectionAverage ρ p u (ε * N) P ≤ 75 * ((N : ℝ) + 2) * B := by
    have h := hproj.trans (hcollision.trans (add_le_add (add_le_add hsmall hsum) hcoarse))
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hpoly : 9 * B + (N : ℝ) * (36 * B) + 2 * B ≤ 75 * ((N : ℝ) + 2) * B := by
      nlinarith
    exact h.trans hpoly
  rw [show -((u : ℝ) - p) = (p : ℝ) - u by ring]
  convert htotal using 1
  dsimp [B, E, H]
  ring

/-- The literal projection-average assertion of Lemma 6.5 after its explicit
polynomial constant is absorbed by the parameter budget. -/
theorem projectionAverage_le_height (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} (hε : 0 ≤ ε) {N p u : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hpu : p ≤ u) (hu : u ≤ N) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) (hbudget : 75 * ((N : ℝ) + 2) ≤ (2 : ℝ) ^ (ε * N)) :
    projectionAverage ρ p u (ε * N) P ≤
      (2 : ℝ) ^ (-((u : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * (profileHeight (regularMeasureExcess ρ N) p p u + 4 * ε)) := by
  apply (projectionAverage_le_explicit_height ρ hρ hε hN hreg hpu hu P hP).trans
  calc
    _ ≤ (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ (3 * (ε * N)) *
        (2 : ℝ) ^ (-((u : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * profileHeight (regularMeasureExcess ρ N) p p u) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget (by positivity))
          (by positivity)) (by positivity)
    _ = _ := by
      simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- The actual passing-test consequence, with the source's extra `R^(2ε)`. -/
theorem projectionCount_le_height_of_passing (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} (hε : 0 ≤ ε) {N p u : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hpu : p ≤ u) (hu : u ≤ N) (P : Fin 2 → ℤ)
    (hP : 0 < unitCellWeight ρ p P) (hbudget : 75 * ((N : ℝ) + 2) ≤ (2 : ℝ) ^ (ε * N))
    {width : ℝ} {w : UnitCircle} (hw : w ∈ projectionPassingDirections ρ p u (ε * N) width P) :
    projectionCount ρ p u (ε * N) width P w ≤
      (2 : ℝ) ^ (-((u : ℝ) - p)) *
        (2 : ℝ) ^ ((N : ℝ) * (profileHeight (regularMeasureExcess ρ N) p p u + 6 * ε)) := by
  have h := mul_le_mul_of_nonneg_left
    (projectionAverage_le_height ρ hρ hε hN hreg hpu hu P hP hbudget)
      (by positivity : 0 ≤ (2 : ℝ) ^ (2 * (ε * N)))
  apply hw.trans
  convert h using 1
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

end FalconerThetaGauge
