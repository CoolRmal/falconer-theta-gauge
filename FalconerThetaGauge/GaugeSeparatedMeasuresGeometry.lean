module

public import FalconerThetaGauge.GaugeSeparatedMeasuresSimilarity
public import Mathlib.Tactic.Module

/-!
# The fixed geometric normalization in Proposition 5.6

An explicit positive similarity places the centers one quarter apart around the
center of the unit square. The selected compact pieces lie in discs of radius
one four-hundredth, and their pair distances lie between `0.24` and `0.26`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerThetaGauge

namespace GaugeSeparatedMeasures

/-- The half-open unit square, with its coordinate description. -/
def unitSquare : Set Plane := {x | ∀ i : Fin 2, x i ∈ Ico (0 : ℝ) 1}

/-- The center of the unit square. -/
def unitSquareCenter : Plane := WithLp.toLp 2 (fun _ : Fin 2 ↦ (1 / 2 : ℝ))

/-- The scale sending the center separation to one quarter. -/
def preparationScale (a b : Plane) : ℝ := (4 * dist a b)⁻¹

/-- The translation sending the midpoint of the two centers to the square center. -/
def preparationTranslation (a b : Plane) : Plane :=
  unitSquareCenter - preparationScale a b • ((1 / 2 : ℝ) • (a + b))

theorem preparationScale_pos {a b : Plane} (hab : a ≠ b) : 0 < preparationScale a b := by
  exact inv_pos.mpr (mul_pos (by norm_num) (dist_pos.mpr hab))

theorem preparationScale_mul_dist {a b : Plane} (hab : a ≠ b) :
    preparationScale a b * dist a b = 1 / 4 := by
  unfold preparationScale
  field_simp [(dist_pos.mpr hab).ne']

theorem preparation_centers_dist {a b : Plane} (hab : a ≠ b) :
    dist (affineMap (preparationScale a b) (preparationTranslation a b) a)
      (affineMap (preparationScale a b) (preparationTranslation a b) b) = 1 / 4 := by
  rw [affineMap_dist (preparationScale_pos hab), preparationScale_mul_dist hab]

theorem preparation_center_dist_squareCenter {a b : Plane} (hab : a ≠ b) :
    dist (affineMap (preparationScale a b) (preparationTranslation a b) a)
        unitSquareCenter = 1 / 8 ∧
      dist (affineMap (preparationScale a b) (preparationTranslation a b) b)
        unitSquareCenter = 1 / 8 := by
  have ha : affineMap (preparationScale a b) (preparationTranslation a b) a -
      unitSquareCenter = preparationScale a b • ((1 / 2 : ℝ) • (a - b)) := by
    unfold affineMap preparationTranslation
    module
  have hb : affineMap (preparationScale a b) (preparationTranslation a b) b -
      unitSquareCenter = preparationScale a b • ((1 / 2 : ℝ) • (b - a)) := by
    unfold affineMap preparationTranslation
    module
  constructor
  · rw [dist_eq_norm, ha, norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (preparationScale_pos hab), Real.norm_eq_abs, abs_of_pos (by norm_num),
      ← dist_eq_norm]
    nlinarith [preparationScale_mul_dist hab]
  · rw [dist_eq_norm, hb, norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (preparationScale_pos hab), Real.norm_eq_abs, abs_of_pos (by norm_num),
      ← dist_eq_norm, dist_comm b a]
    nlinarith [preparationScale_mul_dist hab]

theorem ball_subset_unitSquare {a : Plane} (ha : dist a unitSquareCenter = 1 / 8) :
    Metric.ball a (1 / 400) ⊆ unitSquare := by
  intro x hx i
  have hxc : dist x unitSquareCenter < 1 / 2 := by
    have htri := dist_triangle x a unitSquareCenter
    have hxa := Metric.mem_ball.mp hx
    rw [ha] at htri
    linarith
  have hcoord := PiLp.norm_apply_le (x - unitSquareCenter) i
  simp only [PiLp.sub_apply, unitSquareCenter, ← dist_eq_norm] at hcoord
  have h := abs_lt.mp (hcoord.trans_lt hxc)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Small closed balls become subsets of the source's fixed open preparation discs. -/
theorem preparation_image_subset_ball {a b : Plane} (hab : a ≠ b)
    {A : Set Plane} (hA : A ⊆ Metric.closedBall a (dist a b / 200)) :
    affineMap (preparationScale a b) (preparationTranslation a b) '' A ⊆
      Metric.ball (affineMap (preparationScale a b) (preparationTranslation a b) a)
        (1 / 400) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_ball, affineMap_dist (preparationScale_pos hab)]
  have hdist := mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp (hA hx))
    (preparationScale_pos hab).le
  have hr : preparationScale a b * (dist a b / 200) = 1 / 800 := by
    rw [← mul_div_assoc, preparationScale_mul_dist hab]
    norm_num
  rw [hr] at hdist
  exact hdist.trans_lt (by norm_num)

theorem preparation_image_subset_ball_right {a b : Plane} (hab : a ≠ b)
    {B : Set Plane} (hB : B ⊆ Metric.closedBall b (dist a b / 200)) :
    affineMap (preparationScale a b) (preparationTranslation a b) '' B ⊆
      Metric.ball (affineMap (preparationScale a b) (preparationTranslation a b) b)
        (1 / 400) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_ball, affineMap_dist (preparationScale_pos hab)]
  have hdist := mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp (hB hx))
    (preparationScale_pos hab).le
  have hr : preparationScale a b * (dist a b / 200) = 1 / 800 := by
    rw [← mul_div_assoc, preparationScale_mul_dist hab]
    norm_num
  rw [hr] at hdist
  exact hdist.trans_lt (by norm_num)

/-- The fixed preparation discs have the quantitative separation stated in the manuscript. -/
theorem prepared_balls_distance_bounds {a b : Plane} (hab : dist a b = 1 / 4)
    {x y : Plane} (hx : x ∈ Metric.ball a (1 / 400))
    (hy : y ∈ Metric.ball b (1 / 400)) :
    (24 / 100 : ℝ) ≤ dist x y ∧ dist x y ≤ (26 / 100 : ℝ) := by
  have hxa := Metric.mem_ball.mp hx
  have hyb := Metric.mem_ball.mp hy
  have hlow := dist_triangle4 a x y b
  have hupp := dist_triangle4 x a b y
  rw [dist_comm a x, hab] at hlow
  rw [dist_comm b y, hab] at hupp
  constructor <;> linarith

/-- An injective continuous image transports the probability's compact carrier and support. -/
theorem probabilityMeasure_map_compact_data {μ : ProbabilityMeasure Plane} {K : Set Plane}
    (hK : IsCompact K) (hmass : (μ : Measure Plane) K = 1) {f : Plane → Plane}
    (hf : Continuous f) (hinj : Function.Injective f) :
    (μ.map f : Measure Plane) (f '' K) = 1 ∧
      (μ.map f : Measure Plane).support ⊆ f '' K := by
  have hKimage := hK.image hf
  have hmassimage : (μ.map f : Measure Plane) (f '' K) = 1 := by
    rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply hf.measurable hKimage.measurableSet, preimage_image_eq K hinj]
    exact hmass
  refine ⟨hmassimage, Measure.support_subset_of_isClosed hKimage.isClosed ?_⟩
  rw [mem_ae_iff, measure_compl hKimage.measurableSet (measure_ne_top _ _),
    measure_univ, hmassimage, tsub_self]

end GaugeSeparatedMeasures

open GaugeSeparatedMeasures in
/-- The geometric and energy preparation in Proposition 5.6, using an actual similar copy
of the original compact set. The later radial-density preparation is a separate step. -/
theorem exists_prepared_probabilityMeasures_finite_logCriticalEnergy {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) {E : Set Plane} (hE : IsCompact E)
    (hGauge : 0 < gaugeMeasure θ E) :
    ∃ (ℓ C : ℝ) (z x₀ y₀ : Plane) (S₁ S₂ : Set Plane)
      (μ₁ μ₂ : ProbabilityMeasure Plane),
      0 < ℓ ∧ 0 < C ∧ IsCompact S₁ ∧ IsCompact S₂ ∧
      S₁ ⊆ affineMap ℓ z '' E ∧ S₂ ⊆ affineMap ℓ z '' E ∧
      (μ₁ : Measure Plane) S₁ = 1 ∧ (μ₂ : Measure Plane) S₂ = 1 ∧
      (μ₁ : Measure Plane).support ⊆ S₁ ∧ (μ₂ : Measure Plane).support ⊆ S₂ ∧
      dist x₀ y₀ = 1 / 4 ∧
      S₁ ⊆ Metric.ball x₀ (1 / 400) ∧ S₂ ⊆ Metric.ball y₀ (1 / 400) ∧
      Metric.ball x₀ (1 / 400) ⊆ unitSquare ∧
      Metric.ball y₀ (1 / 400) ⊆ unitSquare ∧
      (∀ x ∈ S₁, ∀ y ∈ S₂,
        (24 / 100 : ℝ) ≤ dist x y ∧ dist x y ≤ (26 / 100 : ℝ)) ∧
      HasGaugeBallBound (μ₁ : Measure Plane) θ C ∧
      HasGaugeBallBound (μ₂ : Measure Plane) θ C ∧
      ∀ γ : ℝ, 1 ≤ γ →
        logCriticalEnergy γ (μ₁ : Measure Plane) ≠ ∞ ∧
          logCriticalEnergy γ (μ₂ : Measure Plane) ≠ ∞ := by
  obtain ⟨μ, C, hC, hmass, _, hball, _⟩ :=
    exists_probabilityMeasure_finite_logCriticalEnergy hθ₀ hθ₁ hE hGauge
  obtain ⟨a, b, A, B, _, _, hab, hA, hB, hAE, hBE, hμA, hμB, hAr, hBr, _⟩ :=
    exists_positive_compact_ball_pair hE
      (by rw [hmass]; exact zero_lt_one)
      (GaugeLogEnergy.measure_singleton_eq_zero hC.le hball)
  have := isProbabilityMeasure_normalizedRestrict hμA.ne' (measure_ne_top _ A)
  have := isProbabilityMeasure_normalizedRestrict hμB.ne' (measure_ne_top _ B)
  let ν₁ : ProbabilityMeasure Plane := ⟨normalizedRestrict (μ : Measure Plane) A, inferInstance⟩
  let ν₂ : ProbabilityMeasure Plane := ⟨normalizedRestrict (μ : Measure Plane) B, inferInstance⟩
  have hball₁ := hasGaugeBallBound_normalizedRestrict hball hμA.ne' (measure_ne_top _ A)
  have hball₂ := hasGaugeBallBound_normalizedRestrict hball hμB.ne' (measure_ne_top _ B)
  have hC₁ : 0 < C / ((μ : Measure Plane) A).toReal :=
    div_pos hC (ENNReal.toReal_pos hμA.ne' (measure_ne_top _ A))
  have hC₂ : 0 < C / ((μ : Measure Plane) B).toReal :=
    div_pos hC (ENNReal.toReal_pos hμB.ne' (measure_ne_top _ B))
  let ℓ := preparationScale a b
  let z := preparationTranslation a b
  let f := affineMap ℓ z
  have hℓ : 0 < ℓ := preparationScale_pos hab
  have hf : Continuous f := continuous_affineMap ℓ z
  have hinj : Function.Injective f := affineMap_injective hℓ z
  let μ₁ := ν₁.map f
  let μ₂ := ν₂.map f
  obtain ⟨C₁, hC₁', hball₁'⟩ :=
    exists_hasGaugeBallBound_map_affine hθ₀ hθ₁ hC₁ hℓ z (μ := ν₁) hball₁
  obtain ⟨C₂, hC₂', hball₂'⟩ :=
    exists_hasGaugeBallBound_map_affine hθ₀ hθ₁ hC₂ hℓ z (μ := ν₂) hball₂
  have hν₁A : (ν₁ : Measure Plane) A = 1 := by
    change normalizedRestrict (μ : Measure Plane) A A = 1
    rw [normalizedRestrict_apply _ A A hA.measurableSet, inter_self,
      ENNReal.inv_mul_cancel hμA.ne' (measure_ne_top _ A)]
  have hν₂B : (ν₂ : Measure Plane) B = 1 := by
    change normalizedRestrict (μ : Measure Plane) B B = 1
    rw [normalizedRestrict_apply _ B B hB.measurableSet, inter_self,
      ENNReal.inv_mul_cancel hμB.ne' (measure_ne_top _ B)]
  have hμ₁data := probabilityMeasure_map_compact_data hA hν₁A hf hinj
  have hμ₂data := probabilityMeasure_map_compact_data hB hν₂B hf hinj
  have hcenters : dist (f a) (f b) = 1 / 4 := preparation_centers_dist hab
  have hAdisc : f '' A ⊆ Metric.ball (f a) (1 / 400) :=
    preparation_image_subset_ball hab hAr
  have hBdisc : f '' B ⊆ Metric.ball (f b) (1 / 400) :=
    preparation_image_subset_ball_right hab hBr
  refine ⟨ℓ, max C₁ C₂, z, f a, f b, f '' A, f '' B, μ₁, μ₂,
    hℓ, hC₁'.trans_le (le_max_left _ _), hA.image hf, hB.image hf,
    image_mono hAE, image_mono hBE, hμ₁data.1, hμ₂data.1, hμ₁data.2, hμ₂data.2,
    hcenters, hAdisc, hBdisc,
    ball_subset_unitSquare (preparation_center_dist_squareCenter hab).1,
    ball_subset_unitSquare (preparation_center_dist_squareCenter hab).2,
    fun x hx y hy ↦ prepared_balls_distance_bounds hcenters (hAdisc hx) (hBdisc hy),
    ?_, ?_, ?_⟩
  · intro x r hr hr1
    exact (hball₁' x r hr hr1).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left C₁ C₂)) _)
  · intro x r hr hr1
    exact (hball₂' x r hr hr1).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right C₁ C₂)) _)
  · intro γ hγ
    exact ⟨logCriticalEnergy_ne_top_of_hasGaugeBallBound hγ hθ₀ hC₁'.le hball₁',
      logCriticalEnergy_ne_top_of_hasGaugeBallBound hγ hθ₀ hC₂'.le hball₂'⟩

end FalconerThetaGauge
