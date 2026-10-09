module

public import FalconerThetaGauge.DistanceLinearizationCells
public import FalconerThetaGauge.ScalarEnergyBinningShift

/-! # Literal center-distance groups have nine-neighbor geometry and width four -/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def linearizationDistanceGroupIndex (p : ℕ) (P Q : Fin 2 → ℤ) : ℤ :=
  scalarBinIndex (dyadicRadius p) (dist (dyadicCellCenter p P) (dyadicCellCenter p Q))

/-- The actual group support has length four fine-cell radii. -/
def linearizationDistanceGroupInterval (p : ℕ) (k : ℤ) : Set ℝ :=
  Ico (((k : ℝ) - 3 / 2) * dyadicRadius p) (((k : ℝ) + 5 / 2) * dyadicRadius p)

theorem abs_dist_sub_cell_centers_le {p : ℕ} {P Q : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q) :
    |dist x y - dist (dyadicCellCenter p P) (dyadicCellCenter p Q)| ≤
      3 / 2 * dyadicRadius p := by
  have heq : (x - y) - (dyadicCellCenter p P - dyadicCellCenter p Q) =
      (x - dyadicCellCenter p P) - (y - dyadicCellCenter p Q) := by abel
  rw [dist_eq_norm, dist_eq_norm]
  calc
    _ ≤ ‖(x - y) - (dyadicCellCenter p P - dyadicCellCenter p Q)‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ _ := by
      rw [heq]
      have hs := pair_cell_displacement_sq_le hx hy
      have hr := dyadicRadius_pos p
      nlinarith [norm_nonneg ((x - dyadicCellCenter p P) - (y - dyadicCellCenter p Q))]

theorem pair_distance_mem_group_interval {p : ℕ} {P Q : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q) :
    dist x y ∈ linearizationDistanceGroupInterval p (linearizationDistanceGroupIndex p P Q) := by
  have hcenter := mem_scalarBin_index (dyadicRadius_pos p)
    (dist (dyadicCellCenter p P) (dyadicCellCenter p Q))
  have herror := abs_le.mp (abs_dist_sub_cell_centers_le hx hy)
  simp only [linearizationDistanceGroupIndex, scalarBin, mem_Ico] at hcenter ⊢
  change ((scalarBinIndex _ _ : ℝ) - 3 / 2) * dyadicRadius p ≤ dist x y ∧
    dist x y < ((scalarBinIndex _ _ : ℝ) + 5 / 2) * dyadicRadius p
  constructor <;> linarith

theorem linearization_group_interval_diameter {p : ℕ} {k : ℤ} {s s' : ℝ}
    (hs : s ∈ linearizationDistanceGroupInterval p k)
    (hs' : s' ∈ linearizationDistanceGroupInterval p k) :
    |s - s'| ≤ 4 * dyadicRadius p := by
  rw [abs_le]
  obtain ⟨hs₁, hs₂⟩ := hs
  obtain ⟨hs'₁, hs'₂⟩ := hs'
  constructor <;> linarith

/-- Actual width-`2⁻ᵗ` collisions can occur only between the nine neighboring
center-distance groups, including all half-open endpoint conventions. -/
theorem linearization_group_collision_neighbors {p t : ℕ} (hpt : p < t)
    {k k' : ℤ} {s s' : ℝ} (hs : s ∈ linearizationDistanceGroupInterval p k)
    (hs' : s' ∈ linearizationDistanceGroupInterval p k')
    (hcollision : |s - s'| ≤ dyadicRadius t) : |k - k'| ≤ 4 := by
  have hpow : dyadicRadius t ≤ dyadicRadius p / 2 := by
    have hcast : (p : ℝ) + 1 ≤ t := by exact_mod_cast hpt
    calc
      _ ≤ (2 : ℝ) ^ (-(p : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by rw [Real.rpow_sub (by norm_num), Real.rpow_one, dyadicRadius]
  obtain ⟨hs₁, hs₂⟩ := hs
  obtain ⟨hs'₁, hs'₂⟩ := hs'
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hcollision
  have hr := dyadicRadius_pos p
  have hl : (k : ℝ) - k' < 9 / 2 := by nlinarith
  have hu : (k' : ℝ) - k < 9 / 2 := by nlinarith
  have hl' : k - k' < 5 := by exact_mod_cast (by linarith : (k : ℝ) - k' < 5)
  have hu' : k' - k < 5 := by exact_mod_cast (by linarith : (k' : ℝ) - k < 5)
  rw [abs_le]
  omega

end FalconerThetaGauge
