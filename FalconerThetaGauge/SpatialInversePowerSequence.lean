/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpatialInversePowerCoefficientBudget
public import Mathlib.Basic.Denumerable

/-! # The ordinary sequence of separated bounded spatial polynomials in Lemma 3.9 -/

@[expose] public section

noncomputable section

open Set Metric

namespace FalconerThetaGauge

def spatialSeparationWordEnumeration : ℕ ≃ SpatialSeparationWord := by
  letI : Infinite SpatialSeparationWord := Infinite.of_injective
    (fun m : ℕ ↦ (⟨m, fun _ ↦ (0, 0)⟩ : SpatialSeparationWord))
    (fun m n h ↦ congrArg Sigma.fst h)
  exact Classical.choice (inferInstance : Nonempty (ℕ ≃ SpatialSeparationWord))

def spatialInversePowerSequenceCoefficient (j : ℕ) (x₀ y₀ : Plane) (ρ : ℝ)
    (n : ℕ) : ℝ :=
  spatialInversePowerCoefficient j x₀ y₀ ρ (spatialSeparationWordEnumeration n)

def spatialInversePowerSequenceLeftPolynomial (x₀ : Plane) (ρ : ℝ) (n : ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  spatialSeparationLeftPolynomial x₀ ρ (spatialSeparationWordEnumeration n)

def spatialInversePowerSequenceRightPolynomial (y₀ : Plane) (ρ : ℝ) (n : ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  spatialSeparationRightPolynomial y₀ ρ (spatialSeparationWordEnumeration n)

def spatialInversePowerSequenceTerm (j : ℕ) (x₀ y₀ : Plane) (ρ : ℝ)
    (n : ℕ) (p : Plane × Plane) : ℝ :=
  spatialInversePowerTerm j x₀ y₀ ρ (spatialSeparationWordEnumeration n) p

theorem spatialInversePowerSequenceTerm_eq (j : ℕ) (x₀ y₀ : Plane) (ρ : ℝ)
    (n : ℕ) (p : Plane × Plane) :
    spatialInversePowerSequenceTerm j x₀ y₀ ρ n p =
      spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n *
    MvPolynomial.eval (fun i ↦ p.1 i) (spatialInversePowerSequenceLeftPolynomial x₀ ρ n) *
    MvPolynomial.eval (fun i ↦ p.2 i)
      (spatialInversePowerSequenceRightPolynomial y₀ ρ n) := rfl

theorem abs_eval_spatialInversePowerSequenceLeftPolynomial_le_one {x₀ x : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ closedBall x₀ ρ) (n : ℕ) :
    |MvPolynomial.eval (fun i ↦ x i)
      (spatialInversePowerSequenceLeftPolynomial x₀ ρ n)| ≤ 1 :=
  abs_eval_spatialSeparationLeftPolynomial_le_one hρ hx _

theorem abs_eval_spatialInversePowerSequenceRightPolynomial_le_one {y₀ y : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hy : y ∈ closedBall y₀ ρ) (n : ℕ) :
    |MvPolynomial.eval (fun i ↦ y i)
      (spatialInversePowerSequenceRightPolynomial y₀ ρ n)| ≤ 1 :=
  abs_eval_spatialSeparationRightPolynomial_le_one hρ hy _

theorem summable_spatialInversePowerSequenceCoefficient_abs (j : ℕ)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    Summable (fun n ↦ |spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n|) :=
  spatialSeparationWordEnumeration.summable_iff.mpr
    (summable_spatialInversePowerCoefficient_abs j hρ hsep)

theorem tsum_spatialInversePowerSequenceCoefficient_abs_le (j : ℕ)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    (∑' n, |spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n|) ≤
      (Real.sqrt 2 / dist x₀ y₀) ^ j := by
  change (∑' n, |spatialInversePowerCoefficient j x₀ y₀ ρ
    (spatialSeparationWordEnumeration n)|) ≤ _
  rw [spatialSeparationWordEnumeration.tsum_eq
    (fun w ↦ |spatialInversePowerCoefficient j x₀ y₀ ρ w|)]
  exact tsum_spatialInversePowerCoefficient_abs_le_sqrt j hρ hsep

theorem hasSum_spatialInversePowerSequenceTerm (j : ℕ) {x₀ y₀ x y : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    (hx : x ∈ closedBall x₀ ρ) (hy : y ∈ closedBall y₀ ρ) :
    HasSum (fun n ↦ spatialInversePowerSequenceTerm j x₀ y₀ ρ n (x, y))
      ((dist x y)⁻¹ ^ j) := by
  change HasSum ((fun w ↦ spatialInversePowerTerm j x₀ y₀ ρ w (x, y)) ∘
    spatialSeparationWordEnumeration) _
  exact spatialSeparationWordEnumeration.hasSum_iff.mpr
    (hasSum_spatialInversePowerTerm j hρ hsep hx hy)

theorem summable_spatialInversePowerSequenceTerm_abs (j : ℕ)
    {x₀ y₀ x y : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀)
    (hx : x ∈ closedBall x₀ ρ) (hy : y ∈ closedBall y₀ ρ) :
    Summable (fun n ↦ |spatialInversePowerSequenceTerm j x₀ y₀ ρ n (x, y)|) := by
  apply (summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep).of_nonneg_of_le
    (fun _ ↦ abs_nonneg _)
  intro n
  exact norm_spatialInversePowerTerm_le j hρ _ ⟨hx, hy⟩

theorem hasSumUniformlyOn_spatialInversePowerSequenceTerm (j : ℕ)
    {x₀ y₀ : Plane} {ρ : ℝ} (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    HasSumUniformlyOn (spatialInversePowerSequenceTerm j x₀ y₀ ρ)
      (fun p : Plane × Plane ↦ (dist p.1 p.2)⁻¹ ^ j)
      (closedBall x₀ ρ ×ˢ closedBall y₀ ρ) := by
  have hu := HasSumUniformlyOn.of_norm_le_summable
    (summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep)
    (fun n p hp ↦ norm_spatialInversePowerTerm_le j hρ
      (spatialSeparationWordEnumeration n) hp)
  apply hu.congr_right
  intro p hp
  exact (hasSum_spatialInversePowerSequenceTerm j hρ hsep hp.1 hp.2).tsum_eq

/-- Lemma 3.9, with explicit real spatial polynomials and a stronger coefficient budget. -/
theorem separated_inverse_powers (j : ℕ) {x₀ y₀ : Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (hsep : 50 * ρ ≤ dist x₀ y₀) :
    ∃ (c : ℕ → ℝ) (f g : ℕ → MvPolynomial (Fin 2) ℝ),
      (∀ n x, x ∈ closedBall x₀ ρ → |MvPolynomial.eval (fun i ↦ x i) (f n)| ≤ 1) ∧
      (∀ n y, y ∈ closedBall y₀ ρ → |MvPolynomial.eval (fun i ↦ y i) (g n)| ≤ 1) ∧
      Summable (fun n ↦ |c n|) ∧
      (∑' n, |c n|) ≤ (Real.sqrt 2 / dist x₀ y₀) ^ j ∧
      HasSumUniformlyOn
        (fun (n : ℕ) (p : Plane × Plane) ↦ c n * MvPolynomial.eval (fun i ↦ p.1 i) (f n) *
          MvPolynomial.eval (fun i ↦ p.2 i) (g n))
        (fun p ↦ (dist p.1 p.2)⁻¹ ^ j) (closedBall x₀ ρ ×ˢ closedBall y₀ ρ) ∧
      (∀ x ∈ closedBall x₀ ρ, ∀ y ∈ closedBall y₀ ρ,
        Summable (fun n ↦ |c n * MvPolynomial.eval (fun i ↦ x i) (f n) *
          MvPolynomial.eval (fun i ↦ y i) (g n)|)) := by
  refine ⟨spatialInversePowerSequenceCoefficient j x₀ y₀ ρ,
    spatialInversePowerSequenceLeftPolynomial x₀ ρ,
    spatialInversePowerSequenceRightPolynomial y₀ ρ, ?_, ?_,
    summable_spatialInversePowerSequenceCoefficient_abs j hρ hsep,
    tsum_spatialInversePowerSequenceCoefficient_abs_le j hρ hsep, ?_, ?_⟩
  · intro n x hx
    exact abs_eval_spatialInversePowerSequenceLeftPolynomial_le_one hρ hx n
  · intro n y hy
    exact abs_eval_spatialInversePowerSequenceRightPolynomial_le_one hρ hy n
  · have heq : spatialInversePowerSequenceTerm j x₀ y₀ ρ =
        (fun (n : ℕ) (p : Plane × Plane) ↦
          spatialInversePowerSequenceCoefficient j x₀ y₀ ρ n *
            MvPolynomial.eval (fun i ↦ p.1 i)
              (spatialInversePowerSequenceLeftPolynomial x₀ ρ n) *
            MvPolynomial.eval (fun i ↦ p.2 i)
              (spatialInversePowerSequenceRightPolynomial y₀ ρ n)) := by
      funext n p
      exact spatialInversePowerSequenceTerm_eq j x₀ y₀ ρ n p
    rw [← heq]
    exact hasSumUniformlyOn_spatialInversePowerSequenceTerm j hρ hsep
  · intro x hx y hy
    simpa only [spatialInversePowerSequenceTerm_eq] using
      summable_spatialInversePowerSequenceTerm_abs j hρ hsep hx hy

end FalconerThetaGauge
