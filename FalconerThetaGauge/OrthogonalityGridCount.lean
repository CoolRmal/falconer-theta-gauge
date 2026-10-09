module

public import FalconerThetaGauge.OrthogonalityTubeCount
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval

/-! # A true finite lattice count for the linked second cell -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped InnerProductSpace Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem norm_sq_eq_inner_quarter_sq_add (v : Plane) (w : UnitCircle) :
    ‖v‖ ^ 2 = (inner ℝ (w : Plane) v) ^ 2 +
      (inner ℝ (circleQuarterTurn w : Plane) v) ^ 2 := by
  have hw : ‖(w : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  have he : ‖directionLineResidual 0 w v‖ ^ 2 = ‖v‖ ^ 2 -
      (inner ℝ (w : Plane) v) ^ 2 := by
    simp only [directionLineResidual, sub_zero]
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hw, Real.norm_eq_abs,
      mul_one, sq_abs, real_inner_comm v (w : Plane)]
    ring
  rw [directionLineResidual_norm_eq_abs_inner_quarterTurn, sub_zero,
    real_inner_comm (circleQuarterTurn w : Plane) v, sq_abs] at he
  linarith

theorem norm_le_three_of_two_coordinates {v : Plane} {w : UnitCircle} {τ : ℝ}
    (hτ : 0 ≤ τ) (h₁ : |inner ℝ (w : Plane) v| ≤ 2 * τ)
    (h₂ : |inner ℝ (circleQuarterTurn w : Plane) v| ≤ 2 * τ) : ‖v‖ ≤ 3 * τ := by
  have hs₁ := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h₁
  have hs₂ := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h₂
  rw [sq_abs] at hs₁ hs₂
  nlinarith [norm_sq_eq_inner_quarter_sq_add v w, norm_nonneg v]

def dyadicCenterBallIndexBox (p : ℕ) (P₀ : Fin 2 → ℤ) (τ : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc
    (P₀ i - (⌈3 * τ * (2 : ℝ) ^ p⌉₊ : ℤ)) (P₀ i + (⌈3 * τ * (2 : ℝ) ^ p⌉₊ : ℤ))

theorem mem_dyadicCenterBallIndexBox {p : ℕ} {P P₀ : Fin 2 → ℤ} {τ : ℝ}
    (h : ‖dyadicCellCenter p P - dyadicCellCenter p P₀‖ ≤ 3 * τ) :
    P ∈ dyadicCenterBallIndexBox p P₀ τ := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  apply Fintype.mem_piFinset.mpr
  intro i
  have hc := (abs_sub_coord_le_dist (dyadicCellCenter p P) (dyadicCellCenter p P₀) i).trans
    (by simpa only [dist_eq_norm] using h)
  have he : (2 : ℝ) ^ p * (dyadicCellCenter p P i - dyadicCellCenter p P₀ i) =
      (P i : ℝ) - (P₀ i : ℝ) := by
    change (2 : ℝ) ^ p * ((((P i : ℝ) + 1 / 2) / (2 : ℝ) ^ p) -
      (((P₀ i : ℝ) + 1 / 2) / (2 : ℝ) ^ p)) = _
    field_simp
    ring
  have hs : |(P i : ℝ) - (P₀ i : ℝ)| ≤ 3 * τ * (2 : ℝ) ^ p := by
    calc
      _ = (2 : ℝ) ^ p * |dyadicCellCenter p P i - dyadicCellCenter p P₀ i| := by
        rw [← he, abs_mul, abs_of_pos hp]
      _ ≤ _ := by nlinarith
  have hh : |(P i : ℝ) - (P₀ i : ℝ)| ≤ (⌈3 * τ * (2 : ℝ) ^ p⌉₊ : ℝ) :=
    hs.trans (Nat.le_ceil (3 * τ * (2 : ℝ) ^ p))
  apply Finset.mem_Icc.mpr
  have hb := abs_le.mp hh
  constructor
  · exact_mod_cast (by linarith :
      (P₀ i : ℝ) - ⌈3 * τ * (2 : ℝ) ^ p⌉₊ ≤ (P i : ℝ))
  · exact_mod_cast (by linarith :
      (P i : ℝ) ≤ (P₀ i : ℝ) + ⌈3 * τ * (2 : ℝ) ^ p⌉₊)

theorem card_dyadicCenterBallIndexBox (p : ℕ) (P₀ : Fin 2 → ℤ) (τ : ℝ) :
    (dyadicCenterBallIndexBox p P₀ τ).card = (2 * ⌈3 * τ * (2 : ℝ) ^ p⌉₊ + 1) ^ 2 := by
  let C := ⌈3 * τ * (2 : ℝ) ^ p⌉₊
  have hi (i : Fin 2) : (Finset.Icc (P₀ i - (C : ℤ)) (P₀ i + (C : ℤ))).card =
      2 * C + 1 := by
    rw [Int.card_Icc]
    have he : P₀ i + (C : ℤ) + 1 - (P₀ i - (C : ℤ)) = ((2 * C + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he, Int.toNat_natCast]
  rw [dyadicCenterBallIndexBox, Fintype.card_piFinset]
  change (∏ i : Fin 2, (Finset.Icc (P₀ i - (C : ℤ)) (P₀ i + (C : ℤ))).card) =
    (2 * C + 1) ^ 2
  simp_rw [hi]
  simp

theorem dyadicCenterBallIndexBox_card_le {p : ℕ} (P₀ : Fin 2 → ℤ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((dyadicCenterBallIndexBox p P₀ τ).card : ℝ) ≤ (6 * τ * (2 : ℝ) ^ p + 3) ^ 2 := by
  rw [card_dyadicCenterBallIndexBox]
  push_cast
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * τ * (2 : ℝ) ^ p)).le
  apply pow_le_pow_left₀ (by positivity)
  linarith

theorem finite_dyadic_center_count_le {p : ℕ} (S : Finset (Fin 2 → ℤ))
    (P₀ : Fin 2 → ℤ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hS : ∀ P ∈ S, ‖dyadicCellCenter p P - dyadicCellCenter p P₀‖ ≤ 3 * τ) :
    (S.card : ℝ) ≤ (6 * τ * (2 : ℝ) ^ p + 3) ^ 2 := by
  have hsub : S ⊆ dyadicCenterBallIndexBox p P₀ τ := fun P hP ↦
    mem_dyadicCenterBallIndexBox (hS P hP)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (dyadicCenterBallIndexBox_card_le P₀ hτ)

/-- A slightly coarser lattice constant, absorbed by the same source tolerance budget. -/
theorem finite_dyadic_link_count_le {p : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (S : Finset (Fin 2 → ℤ)) (P₀ : Fin 2 → ℤ)
    (hS : ∀ P ∈ S, ‖dyadicCellCenter p P - dyadicCellCenter p P₀‖ ≤
      3 * orthogonalityLinkThreshold p E) :
    (S.card : ℝ) ≤ 81 * (2 : ℝ) ^ (3 * E) := by
  have hτ : 0 ≤ orthogonalityLinkThreshold p E := by
    unfold orthogonalityLinkThreshold
    exact mul_nonneg (dyadicRadius_pos p).le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have he : orthogonalityLinkThreshold p E * (2 : ℝ) ^ p = (2 : ℝ) ^ (3 * E / 2) := by
    unfold orthogonalityLinkThreshold dyadicRadius
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    field_simp
  have hb : 1 ≤ (2 : ℝ) ^ (3 * E / 2) := Real.one_le_rpow (by norm_num) (by linarith)
  calc
    _ ≤ (6 * orthogonalityLinkThreshold p E * (2 : ℝ) ^ p + 3) ^ 2 :=
      finite_dyadic_center_count_le S P₀ hτ hS
    _ = (6 * (2 : ℝ) ^ (3 * E / 2) + 3) ^ 2 := by rw [mul_assoc, he]
    _ ≤ (9 * (2 : ℝ) ^ (3 * E / 2)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    _ = _ := by
      rw [mul_pow, show (9 : ℝ) ^ 2 = 81 by norm_num, ← Real.rpow_two,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring

end FalconerThetaGauge
