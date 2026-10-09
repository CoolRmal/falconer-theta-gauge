module

public import FalconerThetaGauge.DistanceLinearizationPassing
public import FalconerThetaGauge.MaskedFourierEnergyReached
public import FalconerThetaGauge.MaskedDistanceEnergyTests

/-! # The actual shorter passing list holds on every retained fine-cell pair -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem retained_pair_passing_pin (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a p : ℕ} {A B P Q : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hP : dyadicCube p P ⊆ dyadicCube a A) (hQ : dyadicCube p Q ⊆ dyadicCube a B)
    (hPocc : P ∈ occupiedUnitCells ρ p) {E width width' : ℝ} (hE : 0 ≤ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width') (test : ProfileScheduleTest)
    (htube : test.kind = .tube → test.endpoint ≤ test.anchor)
    (hprojection : test.kind = .projection → test.anchor ≤ test.endpoint)
    (hanchor : test.anchor ≤ p) (hℓ : a + test.length ≤ p)
    {x y x₀ y₀ : Plane} (hx : x ∈ dyadicCube p P) (hy : y ∈ dyadicCube p Q)
    (hx₀ : x₀ ∈ dyadicCube p P) (hy₀ : y₀ ∈ dyadicCube p Q)
    (hw₀ : (x₀, pairDirection x₀ y₀) ∈ scheduledPassingPinSet ρ E width test) :
    (x, pairDirection x y) ∈ scheduledPassingPinSet ρ E width' test := by
  have hR := occupiedUnitCells_ancestor_of_le ρ hanchor hPocc
  have hxR := mem_dyadicCube_ancestor_of_mem hanchor hx
  have hx₀R := mem_dyadicCube_ancestor_of_mem hanchor hx₀
  apply (mem_scheduledPassingPinSet_on_cell ρ E width' test hR hxR _).2
  exact retained_pair_scheduled_passing ρ hsep hP hQ hE hgap test htube hprojection hℓ
    (Finset.mem_filter.mp hR).2 hx hy hx₀ hy₀
    ((mem_scheduledPassingPinSet_on_cell ρ E width test hR hx₀R _).1 hw₀)

theorem scheduledPassingPinSet_antipodal (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (x : Plane) (w : UnitCircle) :
    (x, circleAntipode w) ∈ scheduledPassingPinSet ρ E width test ↔
      (x, w) ∈ scheduledPassingPinSet ρ E width test := by
  simp only [mem_scheduledPassingPinSet_iff, scheduledPassingDirections_antipodal]

theorem scheduledPassingPinSet_pairDirection_swap (ρ : Measure Plane) (E width : ℝ)
    (test : ProfileScheduleTest) (z : Plane) {x y : Plane} (hxy : x ≠ y) :
    (z, pairDirection y x) ∈ scheduledPassingPinSet ρ E width test ↔
      (z, pairDirection x y) ∈ scheduledPassingPinSet ρ E width test := by
  have hrev : pairDirection y x = circleAntipode (pairDirection x y) := by
    simpa only [pairDirection] using
      pairDirection_eq_circleAntipode_radialProjection hxy.symm
  rw [hrev, scheduledPassingPinSet_antipodal]

/-- This is the genuine source `L'`: only anchor and length restrictions are
assumed, while passing of every actual point pair is proved from the witness. -/
theorem retained_cell_pair_subset_shortened_passing (ρ : Measure Plane) [IsFiniteMeasure ρ]
    {a p : ℕ} {A B P Q : Fin 2 → ℤ} (hsep : SeparatedDyadicCells a A B)
    (hP : dyadicCube p P ⊆ dyadicCube a A) (hQ : dyadicCube p Q ⊆ dyadicCube a B)
    (hPocc : P ∈ occupiedUnitCells ρ p) (hQocc : Q ∈ occupiedUnitCells ρ p)
    {E width width' : ℝ} (hE : 0 ≤ E)
    (hgap : 8 * (2 : ℝ) ^ (-E) ≤ width - width')
    {I₁ I₂ J₁ J₂ : Finset ProfileScheduleTest} (hJ₁ : J₁ ⊆ I₁) (hJ₂ : J₂ ⊆ I₂)
    (hordered₁ : ScheduledTestsOrdered J₁) (hordered₂ : ScheduledTestsOrdered J₂)
    (hshort₁ : ∀ test ∈ J₁, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hshort₂ : ∀ test ∈ J₂, test.anchor ≤ p ∧ a + test.length ≤ p)
    (hwitness : ((dyadicCube p P ×ˢ dyadicCube p Q) ∩
      scheduledPassingPairSet ρ ρ E width I₁ I₂).Nonempty) :
    dyadicCube p P ×ˢ dyadicCube p Q ⊆ scheduledPassingPairSet ρ ρ E width' J₁ J₂ := by
  obtain ⟨⟨x₀, y₀⟩, ⟨hx₀, hy₀⟩, hw₀⟩ := hwitness
  obtain ⟨hw₁, hw₂⟩ := (mem_scheduledPassingPairSet_iff _ _ _ _ _ _ _).mp hw₀
  have hxy₀ : x₀ ≠ y₀ := by
    apply dist_pos.mp
    have hD := (dist_bounds_of_separatedDyadicCells hsep (hP hx₀) (hQ hy₀)).1
    linarith [dyadicRadius_pos a]
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have hxy : x ≠ y := by
    apply dist_pos.mp
    have hD := (dist_bounds_of_separatedDyadicCells hsep (hP hx) (hQ hy)).1
    linarith [dyadicRadius_pos a]
  apply (mem_scheduledPassingPairSet_iff _ _ _ _ _ _ _).mpr
  constructor
  · intro test ht
    exact retained_pair_passing_pin ρ hsep hP hQ hPocc hE hgap test
      (hordered₁.1 test ht) (hordered₁.2 test ht) (hshort₁ test ht).1 (hshort₁ test ht).2
      hx hy hx₀ hy₀ (hw₁ test (hJ₁ ht))
  · intro test ht
    have hswap : SeparatedDyadicCells a B A := by
      simpa only [SeparatedDyadicCells, dist_comm] using hsep
    have h := retained_pair_passing_pin ρ hswap hQ hP hQocc hE hgap test
      (hordered₂.1 test ht) (hordered₂.2 test ht) (hshort₂ test ht).1 (hshort₂ test ht).2
      hy hx hy₀ hx₀
    apply (scheduledPassingPinSet_pairDirection_swap ρ E width' test y hxy).mp
    exact h ((scheduledPassingPinSet_pairDirection_swap ρ E width test y₀ hxy₀).mpr
      (hw₂ test (hJ₂ ht)))

end FalconerThetaGauge
