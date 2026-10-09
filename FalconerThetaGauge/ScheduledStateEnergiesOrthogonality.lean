module

public import FalconerThetaGauge.MaskedFourierOrthogonalityNormalized
public import FalconerThetaGauge.ScheduledStateEnergiesMoveTwoFacts

/-! # Genuine orthogonality refines the actual remaining-list Fourier state -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem sum_occupiedCellPairs_normalized_mass_le_one (ρ : Measure Plane)
    [IsFiniteMeasure ρ] {a p : ℕ} (hap : a ≤ p) {X Y : Fin 2 → ℤ}
    (hX : X ∈ occupiedUnitCells ρ a) (hY : Y ∈ occupiedUnitCells ρ a) :
    (∑ P ∈ (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y),
      (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)) /
        (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y))) ≤ 1 := by
  have hm : 0 < ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y) :=
    mul_pos (mem_filter.mp hX).2 (mem_filter.mp hY).2
  rw [← sum_div, div_le_one hm, Finset.product_eq_sprod, sum_product]
  dsimp only
  simp_rw [← mul_sum]
  rw [← sum_mul]
  exact mul_le_mul (sum_occupiedCellDescendants_le ρ hap X)
    (sum_occupiedCellDescendants_le ρ hap Y)
    (sum_nonneg fun _ _ ↦ measureReal_nonneg) measureReal_nonneg

theorem occupiedCellDescendant_mem_occupied (ρ : Measure Plane) {a p : ℕ}
    {X P : Fin 2 → ℤ} (hP : P ∈ occupiedCellDescendants ρ a p X) :
    P ∈ occupiedUnitCells ρ p := by
  obtain ⟨hunit, _, hmass⟩ := mem_filter.mp hP
  exact mem_filter.mpr ⟨hunit, hmass⟩

theorem sum_maskedFourierEnergy_remaining_le_refined_state (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (A : ℕ → ℝ) (q N : ℕ) (E : ℝ)
    (levels i K : ℕ) {k₀ : ℕ} (hk : k₀ ≤ K) (cutoffK b e : ℕ) {a p : ℕ}
    (hap : a ≤ p) (v : ℕ) {X Y : Fin 2 → ℤ}
    (hX : X ∈ occupiedUnitCells ρ a) (hY : Y ∈ occupiedUnitCells ρ a)
    {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : b₁ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K
      (profileRemainingTests A q N b e a) k₀)
    (hb₂ : b₂ ∈ scheduledSymbolClass ρ E (directionalLevelWidth levels i) K
      (profileRemainingTests A q N b e a) k₀) :
    (∑ P ∈ (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y),
      (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)) /
        (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) *
        maskedFourierEnergy ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ cutoffK v) ≤
      profileFourierStateEnergy ρ A q N E levels i K k₀ cutoffK b e p v := by
  let F := profileFourierStateEnergy ρ A q N E levels i K k₀ cutoffK b e p v
  have hF : 0 ≤ F := profileFourierStateEnergy_nonneg ..
  calc
    _ ≤ ∑ P ∈ (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y),
        (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)) /
          (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) * F := by
      apply sum_le_sum
      intro P hP
      obtain ⟨hP, hQ⟩ := mem_product.mp hP
      have h₁ := maskedFourierEnergy_le_scheduledFourierEnergySup ρ ρ
        (dyadicCube p P.1) (dyadicCube p P.2) E _ K _ _ hk cutoffK v hb₁ hb₂
      have h₂ := scheduledFourierEnergySup_remaining_le_refined_state ρ A q N E
        levels i K hk cutoffK b e hap v (occupiedCellDescendant_mem_occupied ρ hP)
        (occupiedCellDescendant_mem_occupied ρ hQ)
      exact mul_le_mul_of_nonneg_left (h₁.trans h₂) (by positivity)
    _ = (∑ P ∈ (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y),
        (ρ.real (dyadicCube p P.1) * ρ.real (dyadicCube p P.2)) /
          (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y))) * F := by
      rw [sum_mul]
    _ ≤ 1 * F := mul_le_mul_of_nonneg_right
      (sum_occupiedCellPairs_normalized_mass_le_one ρ hap hX hY) hF
    _ = F := one_mul F

theorem profileRemainingTests_ordered (A : ℕ → ℝ) {q N b e a : ℕ}
    (hq : 0 < q) (he : e ≤ N) : ScheduledTestsOrdered (profileRemainingTests A q N b e a) := by
  have hs := profileScheduledTests_ordered A hq he (a := b)
  exact ⟨fun test htest hkind ↦ hs.1 test (mem_filter.mp htest).1 hkind,
    fun test htest hkind ↦ hs.2 test (mem_filter.mp htest).1 hkind⟩

theorem profileFourierStateEnergy_le_orthogonality (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {θ : ℝ} {N b e a g p v : ℕ}
    (hpar : ParameterFacts θ N) (hreg : IsRegularThrough (tolerance θ N) N ρ)
    (he : e ≤ N) (hag : a ≤ g) (hgp : g ≤ p) (hv : v ≤ N) (hpv : p ≤ v)
    (hancestor : (g : ℝ) - a ≤ tolerance θ N * N)
    (hw : 10 * (tolerance θ N * N) ≤ (v : ℝ) - p)
    (hgap : (p : ℝ) - a ≤ (v : ℝ) - p + 2 * (tolerance θ N * N))
    (i : ℕ) (hi : i + 1 ≤ maskLevelCount θ N)
    (htest : (⟨.tube, p, g⟩ : ProfileScheduleTest) ∈
      profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a)
    {L : ℕ} (hL : ∀ test ∈
      profileRemainingTests (regularMeasureExcess ρ N) (blockCount θ N) N b e a,
      test.length ≤ L)
    (hlength : (L : ℝ) ≤ (v : ℝ) - p + 2 * (tolerance θ N * N)) :
    regularMeasureStateEnergy ρ θ N i (.fourier b e a v) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        12 * tolerance θ N)) *
        regularMeasureStateEnergy ρ θ N i (.fourier b e p v) +
      (2 : ℝ) ^ (-(80 * (N : ℝ))) := by
  have hN : 0 < N := by have := hpar.1; omega
  have hq := blockCount_pos θ hN
  have hlevels : 0 < maskLevelCount θ N := by unfold maskLevelCount; omega
  have hcard : (profileRemainingTests (regularMeasureExcess ρ N)
      (blockCount θ N) N b e a).card ≤ N ^ 2 + 1 :=
    (Finset.card_le_card (filter_subset _ _)).trans
      ((profileScheduledTests_card_le_scale_sq (regularMeasureExcess ρ N) hpar he).trans
        (by omega))
  have hap : a ≤ p := hag.trans hgp
  change profileFourierStateEnergy ρ _ _ _ _ _ _ _ _ _ _ _ _ _ ≤ _
  apply finiteEnergyMaximum_le _ _ (by
    have := regularMeasureStateEnergy_nonneg ρ θ N i (.fourier b e p v)
    positivity)
  intro P hP
  obtain ⟨hX, hY⟩ := mem_product.mp hP
  apply csSup_le (scheduledFourierEnergyValues_nonempty ..)
  rintro z ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  have h := maskedFourierEnergy_le_orthogonality ρ hρ hpar hreg hag hgp hv hpv
    hancestor hw hgap hlevels hpar.directional_level_size i
    (directionalLevelWidth_ge_one hlevels hi)
    (profileRemainingTests_ordered _ hq he) htest hcard hL hlength hb₁ hb₂ hX hY
  have hs := sum_maskedFourierEnergy_remaining_le_refined_state ρ
    (regularMeasureExcess ρ N) (blockCount θ N) N (tolerance θ N * N)
    (maskLevelCount θ N) i (8 * expansionCount θ N) (by omega)
    (8 * expansionCount θ N) b e hap v hX hY hb₁ hb₂
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_left hs (by positivity)) le_rfl)


end FalconerThetaGauge
