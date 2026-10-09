module

public import FalconerThetaGauge.DirectionalTestsAveragePairMass

/-! # Finite occupied-center shell estimates with the actual tube-radius truncation -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- The genuine finite dyadic shell bound has no coarse term inside its outer radius. -/
theorem angularCollisionMajorant_le_dyadic_shells_of_norm_le {η : ℝ} (hη : 0 ≤ η)
    {a p : ℕ} (hap : a ≤ p) {v : Plane} (hvouter : ‖v‖ ≤ dyadicRadius a) :
    angularCollisionMajorant η v ≤
      {v : Plane | ‖v‖ ≤ dyadicRadius p}.indicator (fun _ ↦ (1 : ℝ)) v +
        ∑ d ∈ Finset.Ico a p, (η * (2 : ℝ) ^ (d + 1)) *
          {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) v := by
  have hterm (d : ℕ) : 0 ≤ (η * (2 : ℝ) ^ (d + 1)) *
      {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) v := by
    simp only [indicator, mem_ofPred_eq]
    split_ifs <;> positivity
  by_cases hp : ‖v‖ ≤ dyadicRadius p
  · rw [Set.indicator_of_mem (show v ∈ {v : Plane | ‖v‖ ≤ dyadicRadius p} from hp)]
    exact ((angularCollisionMajorant_mem_Icc hη v).2).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun d _ ↦ hterm d)))
  · have hv : v ≠ 0 := by
      intro heq
      simp only [heq, norm_zero] at hp
      exact hp (dyadicRadius_pos p).le
    obtain ⟨d, hd, hdlo, hdhi⟩ := exists_dyadicRadius_shell hap (lt_of_not_ge hp) hvouter
    have hdiv : η / ‖v‖ ≤ η * (2 : ℝ) ^ (d + 1) := by
      calc
        _ ≤ η / dyadicRadius (d + 1) :=
          div_le_div_of_nonneg_left hη (dyadicRadius_pos _) hdlo.le
        _ = _ := by
          rw [dyadicRadius, Real.rpow_neg (by norm_num), div_eq_mul_inv, inv_inv,
            Real.rpow_natCast]
    have hsumd := Finset.single_le_sum (fun d _ ↦ hterm d) hd
    rw [Set.indicator_of_mem (show v ∈ {v : Plane | ‖v‖ ≤ dyadicRadius d} from hdhi), mul_one]
      at hsumd
    rw [Set.indicator_of_notMem (show v ∉ {v : Plane | ‖v‖ ≤ dyadicRadius p} from hp), zero_add]
    apply (show angularCollisionMajorant η v ≤ η / ‖v‖ from ?_).trans (hdiv.trans hsumd)
    simp only [angularCollisionMajorant, ite_eq_right hv]
    exact min_le_right _ _

/-- Actual finite center sums have the same shell bounds, including the optional coarse term. -/
theorem sum_angularCollisionMajorant_le_shells {ι : Type*} (I : Finset ι) (v : ι → Plane)
    {η : ℝ} (hη : 0 ≤ η) {a p : ℕ} (hap : a ≤ p) :
    (∑ q ∈ I, angularCollisionMajorant η (v q)) ≤
      ((I.filter (fun q ↦ ‖v q‖ ≤ dyadicRadius p)).card : ℝ) +
        (∑ d ∈ Finset.Ico a p, (η * (2 : ℝ) ^ (d + 1)) *
          ((I.filter (fun q ↦ ‖v q‖ ≤ dyadicRadius d)).card : ℝ)) +
        η * (2 : ℝ) ^ a * (I.card : ℝ) := by
  have h := Finset.sum_le_sum (fun q (_ : q ∈ I) ↦
    angularCollisionMajorant_le_dyadic_shells hη hap (v q))
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h
  rw [Finset.sum_comm] at h
  have hind (d : ℕ) : (∑ q ∈ I,
      {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) (v q)) =
      ((I.filter (fun q ↦ ‖v q‖ ≤ dyadicRadius d)).card : ℝ) := by
    simp only [indicator, mem_ofPred_eq]
    exact Finset.sum_boole _ _
  simp only [← Finset.mul_sum, hind] at h
  convert h using 1
  ring

theorem sum_angularCollisionMajorant_le_shells_of_norm_le {ι : Type*} (I : Finset ι)
    (v : ι → Plane) {η : ℝ} (hη : 0 ≤ η) {a p : ℕ} (hap : a ≤ p)
    (houter : ∀ q ∈ I, ‖v q‖ ≤ dyadicRadius a) :
    (∑ q ∈ I, angularCollisionMajorant η (v q)) ≤
      ((I.filter (fun q ↦ ‖v q‖ ≤ dyadicRadius p)).card : ℝ) +
        (∑ d ∈ Finset.Ico a p, (η * (2 : ℝ) ^ (d + 1)) *
          ((I.filter (fun q ↦ ‖v q‖ ≤ dyadicRadius d)).card : ℝ)) := by
  have h := Finset.sum_le_sum (fun q hq ↦
    angularCollisionMajorant_le_dyadic_shells_of_norm_le hη hap (houter q hq))
  simp only [Finset.sum_add_distrib] at h
  rw [Finset.sum_comm] at h
  have hind (d : ℕ) : (∑ q ∈ I,
      {v : Plane | ‖v‖ ≤ dyadicRadius d}.indicator (fun _ ↦ (1 : ℝ)) (v q)) =
      ((I.filter (fun q ↦ ‖v q‖ ≤ dyadicRadius d)).card : ℝ) := by
    simp only [indicator, mem_ofPred_eq]
    exact Finset.sum_boole _ _
  simpa only [← Finset.mul_sum, hind] using h

end FalconerThetaGauge
