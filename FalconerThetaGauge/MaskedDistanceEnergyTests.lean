module

public import FalconerThetaGauge.MaskedDistanceEnergy
public import FalconerThetaGauge.DirectionalTestsMaskSupport

/-! # Literal passing pairs for the actual finite scheduled test lists -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman

/-- A pin passes the literal test in its occupied anchor cell at the stated width. -/
def scheduledPassingPinSet (ρ : Measure Plane) (E width : ℝ) (test : ProfileScheduleTest) :
    Set (Plane × UnitCircle) :=
  (⋃ P ∈ occupiedUnitCells ρ test.anchor,
    dyadicCube test.anchor P ×ˢ (scheduledPassingDirections ρ E width test P)ᶜ)ᶜ

theorem measurableSet_scheduledPassingPinSet (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E width : ℝ) (test : ProfileScheduleTest) :
    MeasurableSet (scheduledPassingPinSet ρ E width test) :=
  (MeasurableSet.biUnion (occupiedUnitCells ρ test.anchor).countable_toSet
    (fun P _ ↦ (measurableSet_dyadicCube test.anchor P).prod
      (measurableSet_scheduledPassingDirections ρ E width test P).compl)).compl

theorem mem_scheduledPassingPinSet_iff (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (x : Plane) (w : UnitCircle) :
    (x, w) ∈ scheduledPassingPinSet ρ E width test ↔
      ∀ P ∈ occupiedUnitCells ρ test.anchor, x ∈ dyadicCube test.anchor P →
        w ∈ scheduledPassingDirections ρ E width test P := by
  simp only [scheduledPassingPinSet, mem_compl_iff, mem_iUnion, exists_prop, mem_prod,
    not_exists, not_and, not_not]

/-- On an actual occupied cell, this is precisely the source's passing direction test. -/
theorem mem_scheduledPassingPinSet_on_cell (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) {P : Fin 2 → ℤ} (hP : P ∈ occupiedUnitCells ρ test.anchor)
    {x : Plane} (hx : x ∈ dyadicCube test.anchor P) (w : UnitCircle) :
    (x, w) ∈ scheduledPassingPinSet ρ E width test ↔
      w ∈ scheduledPassingDirections ρ E width test P := by
  rw [mem_scheduledPassingPinSet_iff]
  constructor
  · exact fun h ↦ h P hP hx
  · intro hw Q _ hxQ
    have hQP : Q = P := (mem_dyadicCube_iff.1 hxQ).symm.trans (mem_dyadicCube_iff.1 hx)
    simpa only [hQP] using hw

theorem scheduledPassingPinSet_mono_width (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (E : ℝ) {width width' : ℝ} (hwidth : width ≤ width') (test : ProfileScheduleTest) :
    scheduledPassingPinSet ρ E width' test ⊆ scheduledPassingPinSet ρ E width test := by
  rintro ⟨x, w⟩ hw
  rw [mem_scheduledPassingPinSet_iff] at hw ⊢
  intro P hP hx
  exact scheduledPassingDirections_mono_width ρ E hwidth test P
    (Finset.mem_filter.1 hP).2 (hw P hP hx)

/-- The actual Borel set of directions passing every test at both pins. -/
def scheduledPassingPairSet (ρ₁ ρ₂ : Measure Plane) (E width : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) : Set (Plane × Plane) :=
  (⋂ test ∈ I₁, (fun p : Plane × Plane ↦ (p.1, pairDirection p.1 p.2)) ⁻¹'
    scheduledPassingPinSet ρ₁ E width test) ∩
  (⋂ test ∈ I₂, (fun p : Plane × Plane ↦ (p.2, pairDirection p.1 p.2)) ⁻¹'
    scheduledPassingPinSet ρ₂ E width test)

theorem measurableSet_scheduledPassingPairSet (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (E width : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) :
    MeasurableSet (scheduledPassingPairSet ρ₁ ρ₂ E width I₁ I₂) := by
  apply MeasurableSet.inter
  · exact MeasurableSet.biInter I₁.countable_toSet fun test _ ↦
      (measurableSet_scheduledPassingPinSet ρ₁ E width test).preimage
        (measurable_fst.prodMk measurable_pairDirection)
  · exact MeasurableSet.biInter I₂.countable_toSet fun test _ ↦
      (measurableSet_scheduledPassingPinSet ρ₂ E width test).preimage
        (measurable_snd.prodMk measurable_pairDirection)

theorem mem_scheduledPassingPairSet_iff (ρ₁ ρ₂ : Measure Plane) (E width : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) (p : Plane × Plane) :
    p ∈ scheduledPassingPairSet ρ₁ ρ₂ E width I₁ I₂ ↔
      (∀ test ∈ I₁, (p.1, pairDirection p.1 p.2) ∈ scheduledPassingPinSet ρ₁ E width test) ∧
      (∀ test ∈ I₂, (p.2, pairDirection p.1 p.2) ∈ scheduledPassingPinSet ρ₂ E width test) := by
  simp only [scheduledPassingPairSet, mem_inter_iff, mem_iInter, mem_preimage]

/-- Removing tests and reducing their width enlarges the genuine passing-pair set. -/
theorem scheduledPassingPairSet_mono (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (E : ℝ)
    {width width' : ℝ} (hwidth : width ≤ width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest} (h₁ : J₁ ⊆ I₁) (h₂ : J₂ ⊆ I₂) :
    scheduledPassingPairSet ρ₁ ρ₂ E width' I₁ I₂ ⊆
      scheduledPassingPairSet ρ₁ ρ₂ E width J₁ J₂ := by
  intro p hp
  rw [mem_scheduledPassingPairSet_iff] at hp ⊢
  exact ⟨fun test ht ↦ scheduledPassingPinSet_mono_width ρ₁ E hwidth test (hp.1 test (h₁ ht)),
    fun test ht ↦ scheduledPassingPinSet_mono_width ρ₂ E hwidth test (hp.2 test (h₂ ht))⟩

/-- The exact scheduled version of the source distance energy, with actual test counts. -/
def scheduledDistanceEnergy (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane) (E width : ℝ)
    (I₁ I₂ : Finset ProfileScheduleTest) (t : ℕ) : ℝ :=
  maskedDistanceEnergy ρ₁ ρ₂ X Y (scheduledPassingPairSet ρ₁ ρ₂ E width I₁ I₂) t

/-- Removing actual tests or reducing their width increases the genuine separated energy. -/
theorem scheduledDistanceEnergy_mono (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) (E : ℝ)
    {width width' : ℝ} (hwidth : width ≤ width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest} (h₁ : J₁ ⊆ I₁) (h₂ : J₂ ⊆ I₂) (t : ℕ) :
    scheduledDistanceEnergy ρ₁ ρ₂ X Y E width' I₁ I₂ t ≤
      scheduledDistanceEnergy ρ₁ ρ₂ X Y E width J₁ J₂ t := by
  let : IsFiniteMeasure (passingWeightedDistanceMeasure ρ₁ ρ₂ X Y
      (scheduledPassingPairSet ρ₁ ρ₂ E width J₁ J₂)) :=
    isFiniteMeasure_passingWeightedDistanceMeasure ρ₁ ρ₂ hX hY _
      (fun x hx y hy ↦ crossDistanceWeight_le_of_dist hd (hsep x hx y hy))
  exact maskedDistanceEnergy_mono ρ₁ ρ₂ X Y
    (scheduledPassingPairSet_mono ρ₁ ρ₂ E hwidth h₁ h₂) t

theorem directionalLevelWidth_antitone (I : ℕ) : Antitone (directionalLevelWidth I) := by
  intro i j hij
  unfold directionalLevelWidth
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact sub_le_sub_left (div_le_div_of_nonneg_right hij' (Nat.cast_nonneg I)) 2

/-- The paper's higher-level rule, for the literal equally spaced level widths. -/
theorem scheduledDistanceEnergy_mono_level (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {X Y : Set Plane}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) (E : ℝ) (I : ℕ)
    {i j : ℕ} (hij : i ≤ j) (I₁ I₂ : Finset ProfileScheduleTest) (t : ℕ) :
    scheduledDistanceEnergy ρ₁ ρ₂ X Y E (directionalLevelWidth I i) I₁ I₂ t ≤
      scheduledDistanceEnergy ρ₁ ρ₂ X Y E (directionalLevelWidth I j) I₁ I₂ t :=
  scheduledDistanceEnergy_mono ρ₁ ρ₂ hX hY hd hsep E (directionalLevelWidth_antitone I hij)
    (Finset.Subset.refl I₁) (Finset.Subset.refl I₂) t

end FalconerThetaGauge
