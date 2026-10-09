module

public import FalconerThetaGauge.DirectionalTestsAverageTube
public import FalconerThetaGauge.DirectionalTestsAverageProjectionBound

/-! # The genuine tube-average half of Lemma 6.5, with the source constants -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The two coarse generations in the actual tube radius cost at most `2/N` in excess. -/
theorem regularMeasureExcess_sub_le_tubeHeight (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N g p d : ℕ} (hN : 0 < N) (hgp : g ≤ p)
    (hda : g - 2 ≤ d) (hdp : d ≤ p) :
    regularMeasureExcess ρ N p - regularMeasureExcess ρ N d ≤
      profileHeight (regularMeasureExcess ρ N) p g p + 2 / (N : ℝ) := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  by_cases hgd : g ≤ d
  · have hmin := profileMinimum_le (A := regularMeasureExcess ρ N) hgd hdp
    unfold profileHeight
    have htwo : 0 ≤ 2 / (N : ℝ) := by positivity
    linarith
  · have hdg : d ≤ g := by omega
    have hdg' : (d : ℝ) ≤ g := by exact_mod_cast hdg
    have hdiff : (g : ℝ) - d ≤ 2 := by
      exact_mod_cast (show (g : ℤ) - d ≤ 2 by omega)
    have hlip := regularMeasureExcess_lipschitz ρ hρ hN g d
    rw [abs_of_nonneg (sub_nonneg.mpr hdg')] at hlip
    have hAd : regularMeasureExcess ρ N g - regularMeasureExcess ρ N d ≤ 2 / (N : ℝ) :=
      (le_abs_self _).trans (hlip.trans (div_le_div_of_nonneg_right hdiff hN'.le))
    have hmin := profileMinimum_le (A := regularMeasureExcess ρ N) le_rfl hgp
    unfold profileHeight
    linarith

/-- Exponentiating that precise two-generation loss costs the literal factor four. -/
theorem tube_height_power_le (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {N g p d : ℕ} (hN : 0 < N) (hgp : g ≤ p)
    (hda : g - 2 ≤ d) (hdp : d ≤ p) :
    (2 : ℝ) ^ ((N : ℝ) * (regularMeasureExcess ρ N p - regularMeasureExcess ρ N d)) ≤
      4 * (2 : ℝ) ^ ((N : ℝ) * profileHeight (regularMeasureExcess ρ N) p g p) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_left
      (regularMeasureExcess_sub_le_tubeHeight ρ hρ hN hgp hda hdp) (Nat.cast_nonneg N))
  have hexp : (N : ℝ) * (profileHeight (regularMeasureExcess ρ N) p g p + 2 / (N : ℝ)) =
      (N : ℝ) * profileHeight (regularMeasureExcess ρ N) p g p + 2 := by field_simp
  rw [hexp, Real.rpow_add (by norm_num), show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at h
  simpa only [mul_comm] using h

/-- Literal occupied-center shell counts satisfy the true tube-height budget. -/
theorem occupiedCellCentersInBall_count_le_tubeHeight (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {ε : ℝ} {N g p d : ℕ}
    (hN : 0 < N) (hreg : IsRegularThrough ε N ρ) (hgp : g ≤ p) (hp : p ≤ N)
    (hda : g - 2 ≤ d) (hdp : d ≤ p) (z : Plane) :
    ((occupiedCellCentersInBall ρ p d z).card : ℝ) ≤
      36 * (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ ((p : ℝ) - d) *
        (2 : ℝ) ^ ((N : ℝ) * profileHeight (regularMeasureExcess ρ N) p g p) := by
  apply (occupiedCellCentersInBall_count_le_excess ρ hρ hN hreg hdp hp z).trans
  have h := mul_le_mul_of_nonneg_left (tube_height_power_le ρ hρ hN hgp hda hdp)
    (by positivity : 0 ≤ 9 * (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ ((p : ℝ) - d))
  convert h using 1
  ring

/-- The true tube average before absorbing its explicit polynomial constant. -/
theorem tubeAverage_le_explicit_height (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} (hε : 0 ≤ ε) {N g p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hgp : g ≤ p) (hp : p ≤ N) (P : Fin 2 → ℤ) :
    tubeAverage ρ g p (ε * N) P ≤
      150 * ((N : ℝ) + 4) * (2 : ℝ) ^ (3 * (ε * N)) *
        (2 : ℝ) ^ ((N : ℝ) * profileHeight (regularMeasureExcess ρ N) p g p) := by
  let E : ℝ := ε * N
  let H : ℝ := profileHeight (regularMeasureExcess ρ N) p g p
  let B : ℝ := (2 : ℝ) ^ (3 * E) * (2 : ℝ) ^ ((N : ℝ) * H)
  let η : ℝ := 2 * (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E)
  let I := occupiedTubeRadiusCenters ρ g p P
  let v : (Fin 2 → ℤ) → Plane := fun Q ↦ dyadicCellCenter p Q - dyadicCellCenter p P
  let a := g - 2
  have hap : a ≤ p := (Nat.sub_le g 2).trans hgp
  have hE : 0 ≤ E := mul_nonneg hε (Nat.cast_nonneg N)
  have hH : 0 ≤ H := profileHeight_nonneg hgp le_rfl
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hheight : 1 ≤ (2 : ℝ) ^ ((N : ℝ) * H) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg N) hH)
  have hpowE : (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (3 * E) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsmall : ((I.filter (fun Q ↦ ‖v Q‖ ≤ dyadicRadius p)).card : ℝ) ≤ 9 * B := by
    apply (occupiedTubeRadiusCenters_ball_count_le ρ g p p P).trans
    have h := occupiedCellCentersInBall_count_le_excess ρ hρ hN hreg le_rfl hp
      (dyadicCellCenter p P)
    simp only [sub_self, mul_zero, Real.rpow_zero, mul_one] at h
    apply h.trans
    have h' := mul_le_mul_of_nonneg_left hpowE (by norm_num : (0 : ℝ) ≤ 9)
    have h'' := mul_le_mul_of_nonneg_left hheight (by positivity : 0 ≤ 9 * (2 : ℝ) ^ (3 * E))
    change 9 * (2 : ℝ) ^ E ≤ 9 * B
    dsimp [B]
    nlinarith
  have hterm (d : ℕ) (hd : d ∈ Finset.Ico a p) :
      (η * (2 : ℝ) ^ (d + 1)) * ((I.filter (fun Q ↦ ‖v Q‖ ≤ dyadicRadius d)).card : ℝ) ≤
        144 * B := by
    have hcount := (occupiedTubeRadiusCenters_ball_count_le ρ g p d P).trans
      (occupiedCellCentersInBall_count_le_tubeHeight ρ hρ hN hreg hgp hp
        (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd).2.le (dyadicCellCenter p P))
    have h := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ η * (2 : ℝ) ^ (d + 1))
    have hpowers : (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E) *
        (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ E * (2 : ℝ) ^ ((p : ℝ) - d) = (2 : ℝ) ^ (3 * E) := by
      simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    apply h.trans_eq
    dsimp [η, B]
    rw [pow_succ, ← Real.rpow_natCast (2 : ℝ) d]
    calc
      _ = 144 * ((2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (2 * E) *
          (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ E * (2 : ℝ) ^ ((p : ℝ) - d)) *
            (2 : ℝ) ^ ((N : ℝ) * H) := by ring
      _ = _ := by rw [hpowers]; ring
  have hsum : (∑ d ∈ Finset.Ico a p, (η * (2 : ℝ) ^ (d + 1)) *
      ((I.filter (fun Q ↦ ‖v Q‖ ≤ dyadicRadius d)).card : ℝ)) ≤ (N : ℝ) * (144 * B) := by
    calc
      _ ≤ ∑ _d ∈ Finset.Ico a p, 144 * B := Finset.sum_le_sum hterm
      _ = ((p - a : ℕ) : ℝ) * (144 * B) := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show p - a ≤ N by omega))
        (mul_nonneg (by norm_num) hB)
  have hsumcollision : (∑ Q ∈ I, angularCollisionMajorant η (v Q)) ≤
      9 * B + (N : ℝ) * (144 * B) + 8 * B := by
    by_cases hg : 2 ≤ g
    · have houter : ∀ Q ∈ I, ‖v Q‖ ≤ dyadicRadius a := by
        intro Q hQ
        have h := (Finset.mem_filter.mp hQ).2
        simpa only [four_dyadicRadius_eq_sub_two hg] using h
      have h := (sum_angularCollisionMajorant_le_shells_of_norm_le I v hη hap houter).trans
        (add_le_add hsmall hsum)
      exact h.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) hB))
    · have ha : a = 0 := by dsimp [a]; omega
      have hcard : (I.card : ℝ) ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ (p : ℝ) *
          (4 * (2 : ℝ) ^ ((N : ℝ) * H)) := by
        have hI : (I.card : ℝ) ≤ (occupiedUnitCells ρ p).card :=
          Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
        apply hI.trans ((occupiedUnitCells_count_le_excess ρ hρ hN hreg hp).trans ?_)
        exact mul_le_mul_of_nonneg_left (tube_height_power_le ρ hρ hN hgp
          (by omega : g - 2 ≤ 0) (Nat.zero_le p)) (by positivity)
      have hcoarse : η * (2 : ℝ) ^ a * (I.card : ℝ) ≤ 8 * B := by
        rw [ha, pow_zero, mul_one]
        have h := mul_le_mul_of_nonneg_left hcard hη
        apply h.trans_eq
        dsimp [η, B]
        have hpowers : (2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (p : ℝ) = 1 := by
          rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
        have hEpow : (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ E = (2 : ℝ) ^ (3 * E) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
        calc
          _ = 8 * ((2 : ℝ) ^ (-(p : ℝ)) * (2 : ℝ) ^ (p : ℝ)) *
              ((2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ E) * (2 : ℝ) ^ ((N : ℝ) * H) := by ring
          _ = _ := by rw [hpowers, hEpow]; ring
      exact (sum_angularCollisionMajorant_le_shells I v hη hap).trans
        (add_le_add (add_le_add hsmall hsum) hcoarse)
  have htotal := (tubeAverage_le_sum_collision ρ g p E P).trans hsumcollision
  have hpoly : 9 * B + (N : ℝ) * (144 * B) + 8 * B ≤ 150 * ((N : ℝ) + 4) * B := by
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  have h := htotal.trans hpoly
  convert h using 1
  dsimp [B, E, H]
  ring

/-- The literal tube-average assertion of Lemma 6.5 after absorbing its
explicit polynomial factor with the actual parameter budget. -/
theorem tubeAverage_le_height (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} (hε : 0 ≤ ε) {N g p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hgp : g ≤ p) (hp : p ≤ N) (P : Fin 2 → ℤ)
    (hbudget : 150 * ((N : ℝ) + 4) ≤ (2 : ℝ) ^ (ε * N)) :
    tubeAverage ρ g p (ε * N) P ≤
      (2 : ℝ) ^ ((N : ℝ) * (profileHeight (regularMeasureExcess ρ N) p g p + 4 * ε)) := by
  apply (tubeAverage_le_explicit_height ρ hρ hε hN hreg hgp hp P).trans
  calc
    _ ≤ (2 : ℝ) ^ (ε * N) * (2 : ℝ) ^ (3 * (ε * N)) *
        (2 : ℝ) ^ ((N : ℝ) * profileHeight (regularMeasureExcess ρ N) p g p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget (by positivity))
        (by positivity)
    _ = _ := by
      simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- The actual passing tube count has the source's exact height plus six tolerances. -/
theorem tubeCount_le_height_of_passing (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {ε : ℝ} (hε : 0 ≤ ε) {N g p : ℕ} (hN : 0 < N)
    (hreg : IsRegularThrough ε N ρ) (hgp : g ≤ p) (hp : p ≤ N) (P : Fin 2 → ℤ)
    (hbudget : 150 * ((N : ℝ) + 4) ≤ (2 : ℝ) ^ (ε * N)) {width : ℝ} {w : UnitCircle}
    (hw : w ∈ tubePassingDirections ρ g p (ε * N) width P) :
    tubeCount ρ g p (ε * N) width P w ≤
      (2 : ℝ) ^ ((N : ℝ) * (profileHeight (regularMeasureExcess ρ N) p g p + 6 * ε)) := by
  have h := mul_le_mul_of_nonneg_left
    (tubeAverage_le_height ρ hρ hε hN hreg hgp hp P hbudget)
      (by positivity : 0 ≤ (2 : ℝ) ^ (2 * (ε * N)))
  apply hw.trans
  convert h using 1
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

end FalconerThetaGauge
