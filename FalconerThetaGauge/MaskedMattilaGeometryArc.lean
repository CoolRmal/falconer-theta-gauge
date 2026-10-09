module

public import FalconerThetaGauge.MaskedMattilaCircleInversion
public import FalconerThetaGauge.MaskedDistanceEnergyCells

/-! # The common source arc for actual separated dyadic cells -/

@[expose] public section

noncomputable section

open Set

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem pairDirection_mem_arc_of_relative_displacement {a b x y : Plane}
    (hab : a ≠ b) (hxy : x ≠ y)
    (hclose : ‖(x - y) - (a - b)‖ < dist a b / 50) :
    pairDirection x y ∈ closedDirectionArc (radialAngle b a) (1 / 40) := by
  let u : ℂ := Complex.orthonormalBasisOneI.repr.symm (a - b)
  let v : ℂ := Complex.orthonormalBasisOneI.repr.symm (x - y)
  have hu_norm : ‖u‖ = dist a b := by simp only [u, LinearIsometryEquiv.norm_map, dist_eq_norm]
  have hu : u ≠ 0 := by apply norm_ne_zero_iff.mp; rw [hu_norm]; exact (dist_pos.mpr hab).ne'
  let q : ℂ := v / u
  have hq_close : ‖q - 1‖ < 1 / 50 := by
    change ‖v / u - 1‖ < 1 / 50
    rw [div_sub_one hu, norm_div, hu_norm]
    apply (div_lt_iff₀ (dist_pos.mpr hab)).mpr
    simpa only [v, u, ← map_sub, LinearIsometryEquiv.norm_map, div_eq_mul_inv,
      one_mul, mul_comm] using hclose
  have hq : q ≠ 0 := by
    intro hz
    simp only [hz, zero_sub, norm_neg, norm_one] at hq_close
    norm_num at hq_close
  have hq_angle := abs_arg_lt_one_fortieth_of_norm_sub_one_lt hq_close
  have huv : u * q = v := by dsimp [q]; exact mul_div_cancel₀ v hu
  have hdir : angularDirection (radialAngle b a + q.arg) = (pairDirection x y : Plane) := by
    rw [coe_pairDirection_of_ne hxy]
    change Complex.orthonormalBasisOneI.repr
      ((Real.cos (u.arg + q.arg) + Real.sin (u.arg + q.arg) * Complex.I : ℂ)) =
        ‖x - y‖⁻¹ • (x - y)
    rw [complex_normalized_mul_angle hu hq, huv]
    simp only [v, LinearIsometryEquiv.norm_map, ← Complex.ofReal_inv,
      ← Complex.real_smul, map_smul, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨radialAngle b a + q.arg, ?_, Subtype.ext hdir⟩
  have h := abs_lt.mp hq_angle
  constructor <;> linarith

theorem dist_dyadicCellCenter_le_two_radius {a : ℕ} {P : Fin 2 → ℤ} {x : Plane}
    (hx : x ∈ dyadicCube a P) : dist x (dyadicCellCenter a P) ≤ 2 * dyadicRadius a := by
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by rw [Real.sqrt_le_iff]; norm_num
  apply (dist_le_of_mem_dyadicCube hx (dyadicCellCenter_mem_dyadicCube a P)).trans
  rw [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
    ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hsqrt (by positivity)

/-- One consistently oriented arc of literal angular length `1/20` contains every
pair direction from the actual source-separated dyadic cells. -/
theorem pairDirection_mem_arc_of_separatedDyadicCells {a : ℕ} {P Q : Fin 2 → ℤ}
    (hsep : SeparatedDyadicCells a P Q) {x y : Plane}
    (hx : x ∈ dyadicCube a P) (hy : y ∈ dyadicCube a Q) :
    pairDirection x y ∈ closedDirectionArc
      (radialAngle (dyadicCellCenter a Q) (dyadicCellCenter a P)) (1 / 40) := by
  have hr := dyadicRadius_pos a
  have hab : dyadicCellCenter a P ≠ dyadicCellCenter a Q := by
    apply dist_pos.mp
    linarith [hsep.1]
  have hxy : x ≠ y := by
    apply dist_pos.mp
    linarith [(dist_bounds_of_separatedDyadicCells hsep hx hy).1]
  apply pairDirection_mem_arc_of_relative_displacement hab hxy
  have hx' := dist_dyadicCellCenter_le_two_radius hx
  have hy' := dist_dyadicCellCenter_le_two_radius hy
  have heq : (x - y) - (dyadicCellCenter a P - dyadicCellCenter a Q) =
      (x - dyadicCellCenter a P) - (y - dyadicCellCenter a Q) := by abel
  rw [heq]
  have h := norm_sub_le (x - dyadicCellCenter a P) (y - dyadicCellCenter a Q)
  rw [dist_eq_norm] at hx' hy'
  linarith [hsep.1]

end FalconerThetaGauge
