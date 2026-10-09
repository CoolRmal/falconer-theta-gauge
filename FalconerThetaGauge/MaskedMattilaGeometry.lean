module

public import FalconerThetaGauge.MaskedMattilaGeometryArc
public import FalconerThetaGauge.FourierBilinearFrequencyWindow

/-! # Step 0 distance, frequency and spatial separation bounds from actual geometry -/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem source_pair_distance_lower_cells {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) {x y : Plane}
    (hx : x ∈ dyadicCube a P) (hy : y ∈ dyadicCube a Q) :
    (6 / 25 : ℝ) * (2 : ℝ) ^ (-(a : ℝ)) ≤ ‖x - y‖ := by
  have h := (dist_bounds_of_separatedDyadicCells hsep hx hy).1
  rw [dist_eq_norm, dyadicRadius] at h
  linarith [show 0 < (2 : ℝ) ^ (-(a : ℝ)) by positivity]

theorem source_pair_distance_lower_root {a b x y : Plane} (hab : dist a b = 1 / 4)
    (hx : x ∈ Metric.ball a (1 / 400)) (hy : y ∈ Metric.ball b (1 / 400)) :
    (6 / 25 : ℝ) * (2 : ℝ) ^ (-(0 : ℝ)) ≤ ‖x - y‖ := by
  have h := (prepared_balls_distance_bounds hab hx hy).1
  rw [dist_eq_norm] at h
  norm_num
  linarith

theorem source_frequency_distance_lower {a v : ℕ} {r d : ℝ}
    (hr : r ∈ bilinearFrequencyWindow v)
    (hd : (6 / 25 : ℝ) * (2 : ℝ) ^ (-(a : ℝ)) ≤ d) :
    (2 : ℝ) ^ ((v : ℝ) - a - 4) ≤ r * d := by
  have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ v / 2 := by positivity
  have hr₀ : 0 ≤ r := hbase.trans hr.1
  calc
    _ = (1 / 16 : ℝ) * ((2 : ℝ) ^ v * (2 : ℝ) ^ (-(a : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num),
        show ((v : ℝ) + -(a : ℝ)) = (v : ℝ) - a by ring,
        Real.rpow_sub (by norm_num)]
      norm_num
      ring
    _ ≤ (3 / 25 : ℝ) * ((2 : ℝ) ^ v * (2 : ℝ) ^ (-(a : ℝ))) :=
      mul_le_mul_of_nonneg_right (by norm_num : (1 / 16 : ℝ) ≤ 3 / 25) (by positivity)
    _ = ((2 : ℝ) ^ v / 2) * ((6 / 25 : ℝ) * (2 : ℝ) ^ (-(a : ℝ))) := by ring
    _ ≤ _ := mul_le_mul hr.1 hd (by positivity) hr₀

theorem source_pair_distance_terminal_lower {a N : ℕ} (ha : a ≤ N) {d : ℝ}
    (hd : (6 / 25 : ℝ) * (2 : ℝ) ^ (-(a : ℝ)) ≤ d) :
    (2 : ℝ) ^ (-(N : ℝ) - 4) ≤ d := by
  calc
    _ = (1 / 16 : ℝ) * (2 : ℝ) ^ (-(N : ℝ)) := by
      rw [Real.rpow_sub (by norm_num)]
      norm_num
      ring
    _ ≤ (6 / 25 : ℝ) * (2 : ℝ) ^ (-(a : ℝ)) := by
      apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by
          have ha' : (a : ℝ) ≤ N := by exact_mod_cast ha
          linarith)
    _ ≤ _ := hd

/-- The stronger actual spatial series constant supplies the source's common `6`:
at the root it uses `√2/(1/4) ≤ 6`, while `2/(1/4) ≤ 6` would be false. -/
theorem source_spatial_inverse_coefficient_root {a b : Plane} (hab : dist a b = 1 / 4) :
    Real.sqrt 2 / dist a b ≤ (6 : ℝ) * (2 : ℝ) ^ (0 : ℝ) := by
  have hs : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by rw [Real.sqrt_le_iff]; norm_num
  rw [hab, Real.rpow_zero, mul_one]
  norm_num
  linarith

theorem source_spatial_inverse_coefficient_cells {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) :
    Real.sqrt 2 / dist (dyadicCellCenter a P) (dyadicCellCenter a Q) ≤
      6 * (2 : ℝ) ^ (a : ℝ) := by
  have hr := dyadicRadius_pos a
  have hD : 0 < dist (dyadicCellCenter a P) (dyadicCellCenter a Q) := by linarith [hsep.1]
  have hs : Real.sqrt 2 ≤ (2 : ℝ) := by rw [Real.sqrt_le_iff]; norm_num
  calc
    _ ≤ 2 / (1000 * dyadicRadius a) := div_le_div₀ (by norm_num) hs
      (by positivity) hsep.1
    _ = (1 / 500 : ℝ) * (2 : ℝ) ^ (a : ℝ) := by
      rw [dyadicRadius, Real.rpow_neg (by norm_num)]
      field_simp
      ring
    _ ≤ _ := by gcongr; norm_num

theorem dyadicCube_subset_closedBall_twice_radius (a : ℕ) (P : Fin 2 → ℤ) :
    dyadicCube a P ⊆ Metric.closedBall (dyadicCellCenter a P) (2 * dyadicRadius a) := by
  intro x hx
  exact Metric.mem_closedBall.mpr (dist_dyadicCellCenter_le_two_radius hx)

theorem source_spatial_separated_balls_cells {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) :
    0 < 2 * dyadicRadius a ∧
      50 * (2 * dyadicRadius a) ≤ dist (dyadicCellCenter a P) (dyadicCellCenter a Q) := by
  have hr := dyadicRadius_pos a
  constructor
  · positivity
  · linarith [hsep.1]

theorem source_spatial_separated_balls_root {a b : Plane} (hab : dist a b = 1 / 4) :
    0 < (1 / 400 : ℝ) ∧ 50 * (1 / 400 : ℝ) ≤ dist a b := by
  rw [hab]
  norm_num

end FalconerThetaGauge
