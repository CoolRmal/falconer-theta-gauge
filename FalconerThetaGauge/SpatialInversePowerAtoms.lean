/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpatialInversePowerWordSeries
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # The ten explicit separated monomials of the distance perturbation -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

def spatialSeparationAtomCoefficient (q : ℝ) (c : Fin 2 → ℝ)
    (k : SpatialSeparationAtom) : ℝ :=
  ![2 * q * c k.1, -(2 * q * c k.1), q ^ 2, -(2 * q ^ 2), q ^ 2] k.2

def spatialSeparationAtomLeftPolynomial (k : SpatialSeparationAtom) :
    MvPolynomial (Fin 2) ℝ :=
  ![MvPolynomial.X k.1, 1, MvPolynomial.X k.1 ^ 2, MvPolynomial.X k.1, 1] k.2

def spatialSeparationAtomRightPolynomial (k : SpatialSeparationAtom) :
    MvPolynomial (Fin 2) ℝ :=
  ![1, MvPolynomial.X k.1, 1, MvPolynomial.X k.1, MvPolynomial.X k.1 ^ 2] k.2

def spatialSeparationAtomLeft (u : Fin 2 → ℝ) (k : SpatialSeparationAtom) : ℝ :=
  MvPolynomial.eval u (spatialSeparationAtomLeftPolynomial k)

def spatialSeparationAtomRight (v : Fin 2 → ℝ) (k : SpatialSeparationAtom) : ℝ :=
  MvPolynomial.eval v (spatialSeparationAtomRightPolynomial k)

theorem spatialSeparationAtomLeft_eq (u : Fin 2 → ℝ) (k : SpatialSeparationAtom) :
    spatialSeparationAtomLeft u k = ![u k.1, 1, u k.1 ^ 2, u k.1, 1] k.2 := by
  rcases k with ⟨i, t⟩
  fin_cases t <;> simp [spatialSeparationAtomLeft, spatialSeparationAtomLeftPolynomial]

theorem spatialSeparationAtomRight_eq (v : Fin 2 → ℝ) (k : SpatialSeparationAtom) :
    spatialSeparationAtomRight v k = ![1, v k.1, 1, v k.1, v k.1 ^ 2] k.2 := by
  rcases k with ⟨i, t⟩
  fin_cases t <;> simp [spatialSeparationAtomRight, spatialSeparationAtomRightPolynomial]

theorem abs_spatialSeparationAtomLeft_le_one {u : Fin 2 → ℝ}
    (hu : ∀ i, |u i| ≤ 1) (k : SpatialSeparationAtom) :
    |spatialSeparationAtomLeft u k| ≤ 1 := by
  rw [spatialSeparationAtomLeft_eq]
  rcases k with ⟨i, t⟩
  fin_cases t
  · change |u i| ≤ 1
    exact hu i
  · norm_num
  · change |u i ^ 2| ≤ 1
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hu i)
  · change |u i| ≤ 1
    exact hu i
  · norm_num

theorem abs_spatialSeparationAtomRight_le_one {v : Fin 2 → ℝ}
    (hv : ∀ i, |v i| ≤ 1) (k : SpatialSeparationAtom) :
    |spatialSeparationAtomRight v k| ≤ 1 := by
  rw [spatialSeparationAtomRight_eq]
  rcases k with ⟨i, t⟩
  fin_cases t
  · norm_num
  · change |v i| ≤ 1
    exact hv i
  · norm_num
  · change |v i| ≤ 1
    exact hv i
  · change |v i ^ 2| ≤ 1
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hv i)

theorem sum_spatialSeparationAtomCoefficient_abs {q : ℝ} (hq : 0 ≤ q) (c : Fin 2 → ℝ) :
    (∑ k, |spatialSeparationAtomCoefficient q c k|) =
      4 * q * (|c 0| + |c 1|) + 8 * q ^ 2 := by
  simp only [Fintype.sum_prod_type, spatialSeparationAtomCoefficient]
  simp [Fin.sum_univ_succ, abs_mul, abs_neg, abs_pow, abs_of_nonneg hq]
  ring

theorem sum_spatialSeparationAtomCoefficient_abs_le {q : ℝ} (hq : 0 ≤ q)
    (hqsmall : q ≤ 1 / 50) {c : Fin 2 → ℝ} (hc : ∀ i, |c i| ≤ 1) :
    (∑ k, |spatialSeparationAtomCoefficient q c k|) ≤ 1 / 4 := by
  rw [sum_spatialSeparationAtomCoefficient_abs hq]
  calc
    _ ≤ 8 * q + 8 * q ^ 2 := by nlinarith [hc 0, hc 1]
    _ ≤ 8 * (1 / 50) + 8 * (1 / 50) ^ 2 := by gcongr
    _ ≤ 1 / 4 := by norm_num

def spatialDistancePerturbation (q : ℝ) (c u v : Fin 2 → ℝ) : ℝ :=
  ∑ i, (2 * q * c i * (u i - v i) + q ^ 2 * (u i - v i) ^ 2)

theorem spatialDistancePerturbation_eq_separated_sum (q : ℝ) (c u v : Fin 2 → ℝ) :
    spatialDistancePerturbation q c u v =
      ∑ k, spatialSeparationAtomCoefficient q c k *
        spatialSeparationAtomLeft u k * spatialSeparationAtomRight v k := by
  rw [spatialDistancePerturbation, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  simp only [spatialSeparationAtomCoefficient, spatialSeparationAtomLeft_eq,
    spatialSeparationAtomRight_eq, Fin.sum_univ_succ]
  simp
  ring

def spatialSeparationWordLeftPolynomial (w : SpatialSeparationWord) : MvPolynomial (Fin 2) ℝ :=
  ∏ r, spatialSeparationAtomLeftPolynomial (w.2 r)

def spatialSeparationWordRightPolynomial (w : SpatialSeparationWord) : MvPolynomial (Fin 2) ℝ :=
  ∏ r, spatialSeparationAtomRightPolynomial (w.2 r)

theorem eval_spatialSeparationWordLeftPolynomial (u : Fin 2 → ℝ)
    (w : SpatialSeparationWord) :
    MvPolynomial.eval u (spatialSeparationWordLeftPolynomial w) =
      ∏ r, spatialSeparationAtomLeft u (w.2 r) := by
  simp only [spatialSeparationWordLeftPolynomial, map_prod, spatialSeparationAtomLeft]

theorem eval_spatialSeparationWordRightPolynomial (v : Fin 2 → ℝ)
    (w : SpatialSeparationWord) :
    MvPolynomial.eval v (spatialSeparationWordRightPolynomial w) =
      ∏ r, spatialSeparationAtomRight v (w.2 r) := by
  simp only [spatialSeparationWordRightPolynomial, map_prod, spatialSeparationAtomRight]

theorem abs_eval_spatialSeparationWordLeftPolynomial_le_one {u : Fin 2 → ℝ}
    (hu : ∀ i, |u i| ≤ 1) (w : SpatialSeparationWord) :
    |MvPolynomial.eval u (spatialSeparationWordLeftPolynomial w)| ≤ 1 := by
  rw [eval_spatialSeparationWordLeftPolynomial, Finset.abs_prod]
  exact prod_le_one₀ (fun _ _ ↦ abs_nonneg _)
    (fun _ _ ↦ abs_spatialSeparationAtomLeft_le_one hu _)

theorem abs_eval_spatialSeparationWordRightPolynomial_le_one {v : Fin 2 → ℝ}
    (hv : ∀ i, |v i| ≤ 1) (w : SpatialSeparationWord) :
    |MvPolynomial.eval v (spatialSeparationWordRightPolynomial w)| ≤ 1 := by
  rw [eval_spatialSeparationWordRightPolynomial, Finset.abs_prod]
  exact prod_le_one₀ (fun _ _ ↦ abs_nonneg _)
    (fun _ _ ↦ abs_spatialSeparationAtomRight_le_one hv _)

end FalconerThetaGauge
