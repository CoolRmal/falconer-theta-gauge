module

public import FalconerThetaGauge.StationaryPhaseInverseOperatorsConjugate

/-! # Actual periodicity of the constant-coefficient stationary differential actions -/

@[expose] public section

noncomputable section

open Function Finset Polynomial

namespace FalconerThetaGauge

theorem periodic_iteratedDeriv_complex {G : ℝ → ℂ} {p : ℝ} (hG : Periodic G p) (n : ℕ) :
    Periodic (iteratedDeriv n G) p := by
  have heq : (fun t ↦ G (t + p)) = G := funext hG
  intro t
  have h := congrFun (iteratedDeriv_comp_add_const n G p) t
  rw [heq] at h
  exact h.symm

theorem periodic_polynomialDifferentialAction {G : ℝ → ℂ} {p : ℝ}
    (hG : Periodic G p) (P : Polynomial ℂ) :
    Periodic (polynomialDifferentialAction P G) p := by
  intro t
  simp only [polynomialDifferentialAction, Polynomial.sum_def]
  apply sum_congr rfl
  intro n _
  rw [periodic_iteratedDeriv_complex hG n]

theorem periodic_stationaryPhaseOperator {G : ℝ → ℂ} {p : ℝ}
    (hG : Periodic G p) (j : ℕ) : Periodic (stationaryPhaseOperator j G) p := by
  intro t
  simp only [stationaryPhaseOperator]
  apply sum_congr rfl
  intro n _
  rw [periodic_iteratedDeriv_complex hG n]

theorem periodic_stationaryPhaseConjugateOperator {G : ℝ → ℂ} {p : ℝ}
    (hG : Periodic G p) (j : ℕ) : Periodic (stationaryPhaseConjugateOperator j G) p := by
  intro t
  simp only [stationaryPhaseConjugateOperator]
  apply sum_congr rfl
  intro n _
  rw [periodic_iteratedDeriv_complex hG n]

theorem periodic_stationaryPhaseInverseOperator {G : ℝ → ℂ} {p : ℝ}
    (hG : Periodic G p) (j : ℕ) : Periodic (stationaryPhaseInverseOperator j G) p :=
  periodic_polynomialDifferentialAction hG _

theorem periodic_stationaryPhaseConjugateInverseOperator {G : ℝ → ℂ} {p : ℝ}
    (hG : Periodic G p) (j : ℕ) : Periodic (stationaryPhaseConjugateInverseOperator j G) p :=
  periodic_polynomialDifferentialAction hG _

end FalconerThetaGauge
