module

public import FalconerThetaGauge.FilteredDistanceMeasureGeometry
public import FalconerThetaGauge.ScalarEnergyBinningFourier

/-! # The actual passing weighted distance measure and energy of Definition 7.2 -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal

namespace FalconerThetaGauge

/-- The literal weighted distance pushforward of passing pairs in the two actual carriers. -/
def passingWeightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) : Measure ℝ :=
  filteredCrossDistanceMeasure (ρ₁.restrict X) (ρ₂.restrict Y) (Z.indicator (fun _ ↦ 1))

instance instSFinitePassingWeightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] (X Y : Set Plane) (Z : Set (Plane × Plane)) :
    SFinite (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
  unfold passingWeightedDistanceMeasure filteredCrossDistanceMeasure
  infer_instance

/-- The genuine distance collision energy per unit carrier mass. -/
def maskedDistanceEnergy (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) (t : ℕ) : ℝ :=
  (2 : ℝ) ^ t / (ρ₁.real X * ρ₂.real Y) *
    (scalarCollisionMass (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z)
      (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) ((2 : ℝ) ^ (-(t : ℝ))) 0).toReal

theorem maskedDistanceEnergy_nonneg (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) (t : ℕ) : 0 ≤ maskedDistanceEnergy ρ₁ ρ₂ X Y Z t := by
  unfold maskedDistanceEnergy
  exact mul_nonneg (div_nonneg (by positivity) (by positivity)) ENNReal.toReal_nonneg

/-- This identity identifies the definition with the manuscript's literal restricted pushforward. -/
theorem passingWeightedDistanceMeasure_eq_restrict (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] (X Y : Set Plane) {Z : Set (Plane × Plane)}
    (hZ : MeasurableSet Z) :
    passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z =
      (((ρ₁.prod ρ₂).restrict (Z ∩ (X ×ˢ Y))).withDensity crossDistanceWeight).map
        (fun p : Plane × Plane ↦ dist p.1 p.2) := by
  unfold passingWeightedDistanceMeasure filteredCrossDistanceMeasure
  have heq : (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (Z.indicator (fun _ ↦ 1) p)) =
      Z.indicator crossDistanceWeight := by
    ext p
    by_cases hp : p ∈ Z <;> simp [hp]
  rw [heq, withDensity_indicator hZ, Measure.prod_restrict, Measure.restrict_restrict hZ]

/-- Enlarging the actual passing set enlarges its positive weighted pushforward. -/
theorem passingWeightedDistanceMeasure_mono (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    {Z Z' : Set (Plane × Plane)} (hZZ' : Z ⊆ Z') :
    passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z ≤ passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z' := by
  apply Measure.map_mono _ continuous_dist.measurable
  apply withDensity_mono
  filter_upwards [] with p
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  by_cases hp : p ∈ Z
  · simp [hp, hZZ' hp]
  · by_cases hp' : p ∈ Z' <;> simp [hp, hp']

theorem ae_restricted_product_carriers (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) :
    ∀ᵐ p ∂(ρ₁.restrict X).prod (ρ₂.restrict Y), p.1 ∈ X ∧ p.2 ∈ Y := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (hX.prod hY)

/-- The true singular weight decreases under an actual positive separation bound. -/
theorem crossDistanceWeight_le_of_dist {d : ℝ} (hd : 0 < d) {x y : Plane}
    (hxy : d ≤ dist x y) :
    crossDistanceWeight (x, y) ≤ ENNReal.ofReal ((Real.sqrt d)⁻¹) := by
  rw [crossDistanceWeight_eq_ofReal (dist_pos.mp (hd.trans_le hxy))]
  exact ENNReal.ofReal_le_ofReal
    ((inv_le_inv₀ (Real.sqrt_pos.2 (hd.trans_le hxy)) (Real.sqrt_pos.2 hd)).2
      (Real.sqrt_le_sqrt hxy))

/-- The actual passing measure is bounded by weight times actual carrier masses. -/
theorem passingWeightedDistanceMeasure_univ_le (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (Z : Set (Plane × Plane)) {W : ℝ}
    (hW : ∀ x ∈ X, ∀ y ∈ Y, crossDistanceWeight (x, y) ≤ ENNReal.ofReal W) :
    passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z univ ≤
      ENNReal.ofReal W * (ρ₁ X * ρ₂ Y) := by
  rw [passingWeightedDistanceMeasure, filteredCrossDistanceMeasure_univ]
  calc
    _ ≤ ∫⁻ _p, ENNReal.ofReal W ∂(ρ₁.restrict X).prod (ρ₂.restrict Y) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restricted_product_carriers ρ₁ ρ₂ hX hY] with p hp
      calc
        _ ≤ crossDistanceWeight p * 1 := by
          apply mul_le_mul' le_rfl
          by_cases hz : p ∈ Z <;> simp [hz]
        _ ≤ _ := by simpa only [mul_one] using hW p.1 hp.1 p.2 hp.2
    _ = _ := by
      rw [lintegral_const, ← univ_prod_univ, Measure.prod_prod]
      simp

theorem isFiniteMeasure_passingWeightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (Z : Set (Plane × Plane)) {W : ℝ}
    (hW : ∀ x ∈ X, ∀ y ∈ Y, crossDistanceWeight (x, y) ≤ ENNReal.ofReal W) :
    IsFiniteMeasure (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) :=
  ⟨(passingWeightedDistanceMeasure_univ_le ρ₁ ρ₂ hX hY Z hW).trans_lt (by finiteness)⟩

theorem real_passingWeightedDistanceMeasure_univ_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (Z : Set (Plane × Plane)) {W : ℝ}
    (hW₀ : 0 ≤ W)
    (hW : ∀ x ∈ X, ∀ y ∈ Y, crossDistanceWeight (x, y) ≤ ENNReal.ofReal W) :
    (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z).real univ ≤ W * (ρ₁.real X * ρ₂.real Y) := by
  have h := ENNReal.toReal_mono (by finiteness)
    (passingWeightedDistanceMeasure_univ_le ρ₁ ρ₂ hX hY Z hW)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hW₀] using h

/-- The actual weighted pushforward retains every genuine geometric distance carrier. -/
theorem passingWeightedDistanceMeasure_carrier (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (Z : Set (Plane × Plane))
    {T : Set ℝ} (hT : MeasurableSet T) (hcar : ∀ x ∈ X, ∀ y ∈ Y, dist x y ∈ T) :
    passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z T =
      passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z univ := by
  have hc := ae_restricted_product_carriers ρ₁ ρ₂ hX hY
  have ha : ∀ᵐ p ∂((ρ₁.restrict X).prod (ρ₂.restrict Y)).withDensity
      (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (Z.indicator (fun _ ↦ 1) p)),
      dist p.1 p.2 ∈ T := by
    filter_upwards [(withDensity_absolutelyContinuous ((ρ₁.restrict X).prod (ρ₂.restrict Y))
      (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (Z.indicator (fun _ ↦ 1) p))).ae_le hc]
      with p hp
    exact hcar p.1 hp.1 p.2 hp.2
  rw [passingWeightedDistanceMeasure, filteredCrossDistanceMeasure,
    Measure.map_apply continuous_dist.measurable hT,
    Measure.map_apply continuous_dist.measurable MeasurableSet.univ, preimage_univ]
  exact measure_congr (eventuallyEqSet_univ.2 ha)

theorem scalarCollisionMass_toReal_le_square_mass (η : Measure ℝ) [IsFiniteMeasure η]
    (h u : ℝ) : (scalarCollisionMass η η h u).toReal ≤ (η.real univ) ^ (2 : ℕ) := by
  change (η.prod η).real _ ≤ _
  calc
    _ ≤ (η.prod η).real (univ ×ˢ univ) := measureReal_mono fun _ _ ↦ ⟨trivial, trivial⟩
    _ = _ := by rw [measureReal_prod_prod]; ring

/-- The collision energy is bounded by the squared actual weight bound and carrier masses. -/
theorem maskedDistanceEnergy_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (Z : Set (Plane × Plane)) {W : ℝ}
    (hW₀ : 0 ≤ W)
    (hW : ∀ x ∈ X, ∀ y ∈ Y, crossDistanceWeight (x, y) ≤ ENNReal.ofReal W) (t : ℕ) :
    maskedDistanceEnergy ρ₁ ρ₂ X Y Z t ≤
      (2 : ℝ) ^ t * W ^ (2 : ℕ) * (ρ₁.real X * ρ₂.real Y) := by
  let η := passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z
  let : IsFiniteMeasure η := isFiniteMeasure_passingWeightedDistanceMeasure ρ₁ ρ₂ hX hY Z hW
  let m := ρ₁.real X * ρ₂.real Y
  have hm : 0 ≤ m := by dsimp [m]; positivity
  change (2 : ℝ) ^ t / m * (scalarCollisionMass η η _ _).toReal ≤ (2 : ℝ) ^ t * W ^ 2 * m
  by_cases hm₀ : m = 0
  · simp [hm₀]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm₀)
  have hη : η.real univ ≤ W * m :=
    real_passingWeightedDistanceMeasure_univ_le ρ₁ ρ₂ hX hY Z hW₀ hW
  calc
    _ ≤ (2 : ℝ) ^ t / m * (W * m) ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) hm)
      exact (scalarCollisionMass_toReal_le_square_mass η _ _).trans
        (pow_le_pow_left₀ measureReal_nonneg hη 2)
    _ = _ := by dsimp [m]; field_simp

/-- Positivity of the true measures makes the distance energy monotone in the passing set. -/
theorem maskedDistanceEnergy_mono (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {Z Z' : Set (Plane × Plane)}
    [IsFiniteMeasure (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z')]
    (hZZ' : Z ⊆ Z') (t : ℕ) :
    maskedDistanceEnergy ρ₁ ρ₂ X Y Z t ≤ maskedDistanceEnergy ρ₁ ρ₂ X Y Z' t := by
  let : IsFiniteMeasure (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z) :=
    isFiniteMeasure_of_le (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y Z')
      (passingWeightedDistanceMeasure_mono ρ₁ ρ₂ X Y hZZ')
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (by positivity))
  apply ENNReal.toReal_mono (by unfold scalarCollisionMass; finiteness)
  exact Measure.le_iff.1 (Measure.prod_mono
    (passingWeightedDistanceMeasure_mono ρ₁ ρ₂ X Y hZZ')
    (passingWeightedDistanceMeasure_mono ρ₁ ρ₂ X Y hZZ')) _ (measurableSet_scalarCollision _ _)

end FalconerThetaGauge
