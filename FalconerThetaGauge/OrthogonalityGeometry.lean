module

public import FalconerThetaGauge.EqualArcCutoff
public import FalconerThetaGauge.DirectionalTestsAverageBands
public import FalconerThetaGauge.RegularMeasureExcessGauge

/-! # The literal quarter turn and point-to-center phase errors -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped InnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman

/-- The actual counterclockwise right-angle rotation of the Euclidean plane. -/
def planeQuarterTurn (x : Plane) : Plane :=
  Complex.orthonormalBasisOneI.repr
    (Complex.I * Complex.orthonormalBasisOneI.repr.symm x)

theorem planeQuarterTurn_sub (x y : Plane) :
    planeQuarterTurn (x - y) = planeQuarterTurn x - planeQuarterTurn y := by
  simp only [planeQuarterTurn, map_sub, mul_sub]

theorem norm_planeQuarterTurn (x : Plane) : ‖planeQuarterTurn x‖ = ‖x‖ := by
  simp only [planeQuarterTurn, LinearIsometryEquiv.norm_map, norm_mul, Complex.norm_I, one_mul]

theorem norm_planeQuarterTurn_sub (x y : Plane) :
    ‖planeQuarterTurn x - planeQuarterTurn y‖ = ‖x - y‖ := by
  rw [← planeQuarterTurn_sub, norm_planeQuarterTurn]

def circleQuarterTurn (w : UnitCircle) : UnitCircle :=
  ⟨planeQuarterTurn w, by simpa only [Metric.mem_sphere, dist_zero_right,
    norm_planeQuarterTurn] using w.property⟩

theorem circleQuarterTurn_unitCircleOfAngle (θ : ℝ) :
    circleQuarterTurn (unitCircleOfAngle θ) = unitCircleOfAngle (θ + Real.pi / 2) := by
  apply Subtype.ext
  change planeQuarterTurn (angularDirection θ) = angularDirection (θ + Real.pi / 2)
  simp only [planeQuarterTurn, angularDirection, LinearIsometryEquiv.symm_apply_apply]
  rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  congr 1
  ring_nf
  simp only [Complex.I_sq, neg_one_mul, Complex.ofReal_neg]

/-- A true half-open dyadic cell has half diagonal smaller than three quarters of its side. -/
theorem norm_sub_dyadicCellCenter_le {p : ℕ} {P : Fin 2 → ℤ} {x : Plane}
    (hx : x ∈ dyadicCube p P) : ‖x - dyadicCellCenter p P‖ ≤ 3 / 4 * dyadicRadius p := by
  have hp : 0 < (2 : ℝ) ^ p := by positivity
  have hr : 0 < dyadicRadius p := dyadicRadius_pos p
  have he : (2 : ℝ) ^ p * dyadicRadius p = 1 := by
    rw [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      mul_inv_cancel₀ hp.ne']
  have hcoord (i : Fin 2) : |(x - dyadicCellCenter p P) i| ≤ dyadicRadius p / 2 := by
    have hc : (2 : ℝ) ^ p * dyadicCellCenter p P i = (P i : ℝ) + 1 / 2 := by
      change (2 : ℝ) ^ p * (((P i : ℝ) + 1 / 2) / (2 : ℝ) ^ p) = _
      exact mul_div_cancel₀ _ hp.ne'
    have hs : |(2 : ℝ) ^ p * (x i - dyadicCellCenter p P i)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [(hx i).1, (hx i).2]
    rw [abs_mul, abs_of_pos hp] at hs
    change |x i - dyadicCellCenter p P i| ≤ dyadicRadius p / 2
    nlinarith
  have hsq (i : Fin 2) : ((x - dyadicCellCenter p P) i) ^ 2 ≤
      (dyadicRadius p / 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hcoord i)
  have hn : ‖x - dyadicCellCenter p P‖ ^ 2 ≤ (dyadicRadius p) ^ 2 / 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith [hsq 0, hsq 1]
  nlinarith [norm_nonneg (x - dyadicCellCenter p P)]

theorem norm_sub_le_of_mem_same_dyadicCube {a : ℕ} {X : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube a X) (hy : y ∈ dyadicCube a X) :
    ‖x - y‖ ≤ 3 / 2 * dyadicRadius a := by
  have he : x - y = (x - dyadicCellCenter a X) - (y - dyadicCellCenter a X) := by abel
  rw [he]
  have hh := norm_sub_le (x - dyadicCellCenter a X) (y - dyadicCellCenter a X)
  linarith [norm_sub_dyadicCellCenter_le hx, norm_sub_dyadicCellCenter_le hy]

/-- The exact bilinear phase error after replacing two points and their direction. -/
theorem abs_inner_pair_sub_center_le (x x' c c' : Plane) (w w₀ : UnitCircle) :
    |inner ℝ (w : Plane) (x - x') - inner ℝ (w₀ : Plane) (c - c')| ≤
      ‖x - c‖ + ‖x' - c'‖ + ‖(w : Plane) - (w₀ : Plane)‖ * ‖c - c'‖ := by
  have hw : ‖(w : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  have he : inner ℝ (w : Plane) (x - x') - inner ℝ (w₀ : Plane) (c - c') =
      inner ℝ (w : Plane) ((x - x') - (c - c')) +
      inner ℝ ((w : Plane) - (w₀ : Plane)) (c - c') := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hv : (x - x') - (c - c') = (x - c) - (x' - c') := by abel
  calc
    _ ≤ |inner ℝ (w : Plane) ((x - x') - (c - c'))| +
        |inner ℝ ((w : Plane) - (w₀ : Plane)) (c - c')| := by rw [he]; exact abs_add_le _ _
    _ ≤ ‖(w : Plane)‖ * ‖(x - x') - (c - c')‖ +
        ‖(w : Plane) - (w₀ : Plane)‖ * ‖c - c'‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ _ := by rw [hw, one_mul, hv]; gcongr; exact norm_sub_le _ _

end FalconerThetaGauge
