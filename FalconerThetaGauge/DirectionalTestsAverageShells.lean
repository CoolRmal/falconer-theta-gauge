module

public import FalconerThetaGauge.DirectionalTestsAverageProjection
public import FalconerThetaGauge.DirectionalTestsAverageGridCount

/-! # Genuine finite dyadic shell bounds for the capped inverse-distance pair kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- A true finite dyadic shell containing any positive radius in a dyadic annulus. -/
theorem exists_dyadicRadius_shell {p u : ℕ} (hpu : p ≤ u) {r : ℝ}
    (hr : dyadicRadius u < r) (hp : r ≤ dyadicRadius p) :
    ∃ d ∈ Finset.Ico p u, dyadicRadius (d + 1) < r ∧ r ≤ dyadicRadius d := by
  induction u with
  | zero =>
    have heq : p = 0 := by omega
    subst p
    exact (not_lt_of_ge hp hr).elim
  | succ u ih =>
    by_cases hpu' : p ≤ u
    · by_cases hu : r ≤ dyadicRadius u
      · exact ⟨u, Finset.mem_Ico.mpr ⟨hpu', by omega⟩, hr, hu⟩
      · obtain ⟨d, hd, hdlo, hdhi⟩ := ih hpu' (lt_of_not_ge hu)
        exact ⟨d, Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hd).1,
          by have := (Finset.mem_Ico.mp hd).2; omega⟩, hdlo, hdhi⟩
    · have heq : p = u + 1 := by omega
      subst p
      exact (not_lt_of_ge hp hr).elim

/-- Literal pair-distance closed balls, including the diagonal. -/
def dyadicPairBall (d : ℕ) : Set (Plane × Plane) :=
  {zz | ‖zz.1 - zz.2‖ ≤ dyadicRadius d}

theorem measurableSet_dyadicPairBall (d : ℕ) : MeasurableSet (dyadicPairBall d) :=
  (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const).measurableSet

/-- A finite, genuine pointwise shell decomposition bound. The coarse term
is harmless, and the diagonal is kept in the small-distance indicator. -/
theorem angularCollisionMajorant_le_dyadic_shells {η : ℝ} (hη : 0 ≤ η) {p u : ℕ}
    (hpu : p ≤ u) (v : Plane) :
    angularCollisionMajorant η v ≤
      {v : Plane | ‖v‖ ≤ dyadicRadius u}.indicator (fun _ ↦ (1 : ℝ)) v +
        (∑ d ∈ Finset.Ico p u, (η * (2 : ℝ) ^ (d + 1)) *
          {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) v) +
        η * (2 : ℝ) ^ p := by
  have hterm (d : ℕ) : 0 ≤ (η * (2 : ℝ) ^ (d + 1)) *
      {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) v := by
    simp only [indicator, mem_ofPred_eq]
    split_ifs <;> positivity
  have hsum : 0 ≤ ∑ d ∈ Finset.Ico p u, (η * (2 : ℝ) ^ (d + 1)) *
      {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) v :=
    Finset.sum_nonneg (fun d _ ↦ hterm d)
  have hcoarse : 0 ≤ η * (2 : ℝ) ^ p := by positivity
  by_cases hu : ‖v‖ ≤ dyadicRadius u
  · rw [Set.indicator_of_mem (show v ∈ {v : Plane | ‖v‖ ≤ dyadicRadius u} from hu)]
    have h := (angularCollisionMajorant_mem_Icc hη v).2
    linarith
  · have hv : v ≠ 0 := by
      intro heq
      simp only [heq, norm_zero] at hu
      exact hu (dyadicRadius_pos u).le
    have hmaj : angularCollisionMajorant η v ≤ η / ‖v‖ := by
      simp only [angularCollisionMajorant, ite_eq_right hv]
      exact min_le_right _ _
    by_cases hp : ‖v‖ ≤ dyadicRadius p
    · obtain ⟨d, hd, hdlo, hdhi⟩ := exists_dyadicRadius_shell hpu (lt_of_not_ge hu) hp
      have hdiv : η / ‖v‖ ≤ η * (2 : ℝ) ^ (d + 1) := by
        calc
          _ ≤ η / dyadicRadius (d + 1) :=
            div_le_div_of_nonneg_left hη (dyadicRadius_pos _) hdlo.le
          _ = _ := by
            rw [dyadicRadius, Real.rpow_neg (by norm_num),
              div_eq_mul_inv, inv_inv, Real.rpow_natCast]
      have hone : {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) v = 1 := by
        simp only [indicator, mem_ofPred_eq, hdhi, ite_true]
      have hsumd := Finset.single_le_sum (fun d _ ↦ hterm d) hd
      rw [hone, mul_one] at hsumd
      simp only [indicator, mem_ofPred_eq, hu, ite_false, zero_add]
      exact (hmaj.trans hdiv).trans (hsumd.trans (le_add_of_nonneg_right hcoarse))
    · have hdiv : η / ‖v‖ ≤ η * (2 : ℝ) ^ p := by
        calc
          _ ≤ η / dyadicRadius p := div_le_div_of_nonneg_left hη
            (dyadicRadius_pos p) (le_of_not_ge hp)
          _ = _ := by
            rw [dyadicRadius, Real.rpow_neg (by norm_num), div_eq_mul_inv, inv_inv,
              Real.rpow_natCast]
      simp only [indicator, mem_ofPred_eq, hu, ite_false, zero_add]
      exact (hmaj.trans hdiv).trans (le_add_of_nonneg_left hsum)

/-- Exact finite-shell integration against the actual pair probability. -/
theorem integral_angularCollisionMajorant_le_dyadic_shells (ν : Measure Plane)
    [IsProbabilityMeasure ν] {η : ℝ} (hη : 0 ≤ η) {p u : ℕ} (hpu : p ≤ u) :
    (∫ zz : Plane × Plane, angularCollisionMajorant η (zz.1 - zz.2) ∂ν.prod ν) ≤
      (ν.prod ν).real (dyadicPairBall u) +
        (∑ d ∈ Finset.Ico p u, (η * (2 : ℝ) ^ (d + 1)) * (ν.prod ν).real (dyadicPairBall d)) +
        η * (2 : ℝ) ^ p := by
  have hb (d : ℕ) : Integrable ((dyadicPairBall d).indicator (fun _ ↦ (1 : ℝ))) (ν.prod ν) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_dyadicPairBall d)
  have hsum : Integrable (fun zz : Plane × Plane ↦ ∑ d ∈ Finset.Ico p u,
      (η * (2 : ℝ) ^ (d + 1)) * (dyadicPairBall d).indicator (fun _ ↦ (1 : ℝ)) zz)
      (ν.prod ν) := integrable_finsetSum _ (fun d _ ↦ (hb d).const_mul _)
  have hbound := integral_mono (integrable_angularCollisionMajorant_pair ν hη)
    (((hb u).add hsum).add (integrable_const (η * (2 : ℝ) ^ p)))
    (fun zz ↦ angularCollisionMajorant_le_dyadic_shells hη hpu (zz.1 - zz.2))
  change (∫ zz : Plane × Plane, angularCollisionMajorant η (zz.1 - zz.2) ∂ν.prod ν) ≤
    ∫ zz, (dyadicPairBall u).indicator (fun _ ↦ (1 : ℝ)) zz +
      (∑ d ∈ Finset.Ico p u, (η * (2 : ℝ) ^ (d + 1)) *
        (dyadicPairBall d).indicator (fun _ ↦ (1 : ℝ)) zz) + η * (2 : ℝ) ^ p ∂ν.prod ν at hbound
  rw [integral_add (f := fun zz ↦ (dyadicPairBall u).indicator (fun _ ↦ (1 : ℝ)) zz +
      ∑ d ∈ Finset.Ico p u, (η * (2 : ℝ) ^ (d + 1)) *
        (dyadicPairBall d).indicator (fun _ ↦ (1 : ℝ)) zz)
      ((hb u).add hsum) (integrable_const _),
    integral_add (f := fun zz ↦ (dyadicPairBall u).indicator (fun _ ↦ (1 : ℝ)) zz) (hb u) hsum,
    integral_finsetSum _ (fun d _ ↦ (hb d).const_mul _)] at hbound
  have huniv : (ν.prod ν).real univ = 1 := by
    simp only [Measure.real, measure_univ, ENNReal.toReal_one]
  simpa only [integral_const_mul, integral_indicator_const _ (measurableSet_dyadicPairBall _),
    integral_const, huniv, smul_eq_mul, one_mul, mul_one] using hbound

end FalconerThetaGauge
