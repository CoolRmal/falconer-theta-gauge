/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.MaskedMattilaWindowEstimate
public import FalconerThetaGauge.MaskedDistanceEnergyDyadic

/-! # Genuine reduction of both Fourier signs to the positive Mattila window -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter

namespace FalconerThetaGauge

theorem norm_angularScalarFourier_neg (η : Measure ℝ) (r : ℝ) :
    ‖angularScalarFourier η (-r)‖ = ‖angularScalarFourier η r‖ := by
  simp [angularScalarFourier, charFun_neg]

theorem scalarDyadicFourierShellIntegral_le_twice_window (η : Measure ℝ)
    [IsFiniteMeasure η] (v : ℕ) :
    scalarDyadicFourierShellIntegral η v ≤
      2 * ∫ r in bilinearFrequencyWindow v, ‖angularScalarFourier η r‖ ^ 2 := by
  let f := fun r ↦ ‖angularScalarFourier η r‖ ^ 2
  let A := (2 : ℝ) ^ v / 2
  let B := 2 * (2 : ℝ) ^ v
  have hA : 0 < A := by positivity
  have hAB : A ≤ B := by dsimp [A, B]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) v]
  have hf : Continuous f := (continuous_angularScalarFourier η).norm.pow 2
  have hI : IntegrableOn f (Icc A B) := hf.integrableOn_Icc
  have hJ : IntegrableOn f (Icc (-B) (-A)) := hf.integrableOn_Icc
  have hdis : Disjoint (Icc A B) (Icc (-B) (-A)) := by
    apply Set.disjoint_left.mpr
    intro r hr hs
    linarith [hr.1, hs.2]
  have hsub : scalarDyadicFourierShell v ⊆ Icc A B ∪ Icc (-B) (-A) := by
    intro r hr
    have hlow : A ≤ |r| := by
      simpa only [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast,
        Real.rpow_one] using hr.1
    have hu : |r| ≤ (2 : ℝ) ^ v := hr.2
    by_cases hs : 0 ≤ r
    · left
      rw [abs_of_nonneg hs] at hlow hu
      constructor
      · exact hlow
      · dsimp [B]; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) v]
    · right
      rw [abs_of_neg (lt_of_not_ge hs)] at hlow hu
      constructor
      · dsimp [B]; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) v]
      · linarith
  have heven : (fun r ↦ f (-r)) = f := by
    funext r
    exact congrArg (fun x : ℝ ↦ x ^ 2) (norm_angularScalarFourier_neg η r)
  have hneg : (∫ r in Icc (-B) (-A), f r) = ∫ r in Icc A B, f r := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -B ≤ -A),
      ← intervalIntegral.integral_of_le hAB]
    have he := intervalIntegral.integral_comp_neg f (a := A) (b := B)
    rw [heven] at he
    exact he.symm
  calc
    _ ≤ ∫ r in Icc A B ∪ Icc (-B) (-A), f r := by
      apply setIntegral_mono_set (hI.union hJ)
      · exact Eventually.of_forall (fun _ ↦ sq_nonneg _)
      · exact Eventually.of_forall hsub
    _ = (∫ r in Icc A B, f r) + ∫ r in Icc (-B) (-A), f r :=
      setIntegral_union hdis measurableSet_Icc hI hJ
    _ = _ := by rw [hneg]; dsimp [bilinearFrequencyWindow, A, B, f]; ring

theorem mattila_shell_error_budget {N v : ℕ} (hN : 1 ≤ N) (hv : v ≤ N) :
    6 * (2 : ℝ) ^ v * ((2 : ℝ) ^ (-(200 * (N : ℝ)))) ^ 2 ≤
      (2 : ℝ) ^ (-(390 * (N : ℝ))) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hvreal : (v : ℝ) ≤ N := by exact_mod_cast hv
  have h6 : (6 : ℝ) ≤ (2 : ℝ) ^ (9 * (N : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ (9 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    _ ≤ (2 : ℝ) ^ (9 * (N : ℝ)) * (2 : ℝ) ^ (v : ℝ) *
        ((2 : ℝ) ^ (-(200 * (N : ℝ)))) ^ 2 := by
      rw [Real.rpow_natCast]
      gcongr
    _ = (2 : ℝ) ^ (9 * (N : ℝ) + v - 400 * (N : ℝ)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end FalconerThetaGauge
