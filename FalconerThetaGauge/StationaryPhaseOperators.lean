/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.StationaryMorseAngle
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Exact constant coefficients for the circular Morse coordinate

The coefficients are finite sums of the actual derivatives of the literal Morse angle and
Jacobian. Ordered finite partitions supply the composition coefficients; Leibniz supplies
the Jacobian factor. They are independent of the amplitude and the stationary point.
-/

@[expose] public section

noncomputable section

open Finset Set
open scoped ContDiff Topology

namespace FalconerThetaGauge

/-- The coefficient of the `k`th derivative in the `m`th derivative of a composition. -/
def stationaryCompositionCoefficient (m k : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m,
    if c.length = k then ∏ r, iteratedDeriv (c.partSize r) stationaryMorseAngle 0 else 0

/-- Universal real coefficients for the amplitude times the Morse Jacobian. -/
def stationaryDerivativeCoefficient (n k : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1),
    (n.choose i : ℝ) * iteratedDeriv i stationaryMorseJacobian 0 *
      stationaryCompositionCoefficient (n - i) k

theorem stationaryCompositionCoefficient_eq_zero {m k : ℕ} (hk : m < k) :
    stationaryCompositionCoefficient m k = 0 := by
  classical
  apply sum_eq_zero
  intro c _
  have hne : c.length ≠ k := by have := c.length_le; omega
  simp [hne]

theorem stationaryCompositionCoefficient_zero (k : ℕ) :
    stationaryCompositionCoefficient 0 k = if k = 0 then 1 else 0 := by
  classical
  simp [stationaryCompositionCoefficient, OrderedFinpartition.default_eq,
    OrderedFinpartition.atomic, eq_comm]

theorem stationaryDerivativeCoefficient_zero : stationaryDerivativeCoefficient 0 0 = 1 := by
  simp [stationaryDerivativeCoefficient, stationaryCompositionCoefficient_zero,
    stationaryMorseJacobian]

theorem stationaryDerivativeCoefficient_eq_zero {n k : ℕ} (hk : n < k) :
    stationaryDerivativeCoefficient n k = 0 := by
  classical
  unfold stationaryDerivativeCoefficient
  apply sum_eq_zero
  intro i _
  rw [stationaryCompositionCoefficient_eq_zero (by omega : n - i < k)]
  simp

/-- Exact Faà di Bruno coefficients, valid for real or complex amplitudes. -/
theorem iteratedDeriv_stationaryMorse_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ → E} {φ : ℝ} {n m : ℕ} (hm : m ≤ n) (hG : ContDiffAt ℝ n G φ) :
    iteratedDeriv m (fun s => G (φ + stationaryMorseAngle s)) 0 =
      ∑ k ∈ range (n + 1), stationaryCompositionCoefficient m k • iteratedDeriv k G φ := by
  classical
  have hθ : ContDiffAt ℝ n stationaryMorseAngle 0 :=
    (contDiffAt_stationaryMorseAngle (by norm_num)).of_le (by simp)
  have hinner : ContDiffAt ℝ n (fun s => φ + stationaryMorseAngle s) 0 :=
    contDiffAt_const.add hθ
  have hG' : ContDiffAt ℝ n G (φ + stationaryMorseAngle 0) := by
    simpa [stationaryMorseAngle_zero] using hG
  rw [show (fun s => G (φ + stationaryMorseAngle s)) =
    G ∘ (fun s => φ + stationaryMorseAngle s) from rfl,
    iteratedDeriv_scomp_eq_sum_orderedFinpartition
      (f := fun s => φ + stationaryMorseAngle s) (g := G) (x := 0) (i := m)
      hG' hinner (by exact_mod_cast hm)]
  simp only [stationaryMorseAngle_zero, add_zero]
  simp_rw [iteratedDeriv_const_add (OrderedFinpartition.partSize_pos _ _) φ]
  symm
  simp only [stationaryCompositionCoefficient, sum_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  have hc : c.length ∈ range (n + 1) := mem_range.mpr (by have := c.length_le; omega)
  simp [ite_smul, hc]

theorem iteratedDeriv_stationaryMorseJacobian_ofReal (n : ℕ) :
    iteratedDeriv n (fun s => (stationaryMorseJacobian s : ℂ)) 0 =
      ((iteratedDeriv n stationaryMorseJacobian (0 : ℝ) : ℝ) : ℂ) := by
  have hJ : ContDiffAt ℝ n stationaryMorseJacobian 0 :=
    (contDiffAt_stationaryMorseJacobian (by norm_num)).of_le (by simp)
  simpa only [Complex.real_smul, mul_one] using iteratedDeriv_smul_const hJ (1 : ℂ)

/-- The exact constant-coefficient representation in source Lemma 3.6. -/
theorem iteratedDeriv_stationaryMorse_weighted
    {G : ℝ → ℂ} {φ : ℝ} {n : ℕ} (hG : ContDiffAt ℝ n G φ) :
    iteratedDeriv n
        (fun s => G (φ + stationaryMorseAngle s) * stationaryMorseJacobian s) 0 =
      ∑ k ∈ range (n + 1), (stationaryDerivativeCoefficient n k : ℂ) *
        iteratedDeriv k G φ := by
  classical
  have hθ : ContDiffAt ℝ n stationaryMorseAngle 0 :=
    (contDiffAt_stationaryMorseAngle (by norm_num)).of_le (by simp)
  have hJ : ContDiffAt ℝ n stationaryMorseJacobian 0 :=
    (contDiffAt_stationaryMorseJacobian (by norm_num)).of_le (by simp)
  have hJc : ContDiffAt ℝ n (fun s => (stationaryMorseJacobian s : ℂ)) 0 := by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hJ
  have hGc : ContDiffAt ℝ n (fun s => G (φ + stationaryMorseAngle s)) 0 := by
    have hG' : ContDiffAt ℝ n G (φ + stationaryMorseAngle 0) := by
      simpa [stationaryMorseAngle_zero] using hG
    exact hG'.comp 0 (contDiffAt_const.add hθ)
  rw [show (fun s => G (φ + stationaryMorseAngle s) * stationaryMorseJacobian s) =
    (fun s => (stationaryMorseJacobian s : ℂ) * G (φ + stationaryMorseAngle s)) from
      funext (fun s => mul_comm _ _), iteratedDeriv_fun_mul hJc hGc]
  simp_rw [iteratedDeriv_stationaryMorseJacobian_ofReal,
    iteratedDeriv_stationaryMorse_comp (Nat.sub_le n _) hG,
    Finset.mul_sum, Complex.real_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  simp only [stationaryDerivativeCoefficient, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_natCast, Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- The same exact formula with the derivative of the angle, as written in the source. -/
theorem iteratedDeriv_stationaryMorse_weighted_deriv
    {G : ℝ → ℂ} {φ : ℝ} {n : ℕ} (hG : ContDiffAt ℝ n G φ) :
    iteratedDeriv n
        (fun s => G (φ + stationaryMorseAngle s) * deriv stationaryMorseAngle s) 0 =
      ∑ k ∈ range (n + 1), (stationaryDerivativeCoefficient n k : ℂ) *
        iteratedDeriv k G φ := by
  have heq : (fun s => G (φ + stationaryMorseAngle s) * deriv stationaryMorseAngle s) =ᶠ[𝓝 0]
      (fun s => G (φ + stationaryMorseAngle s) * stationaryMorseJacobian s) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2)] with s hs
    rw [deriv_stationaryMorseAngle hs]
  rw [heq.iteratedDeriv_eq n]
  exact iteratedDeriv_stationaryMorse_weighted hG

end FalconerThetaGauge
