module

public import FalconerThetaGauge.OrthogonalityTubeGeometry
public import FalconerThetaGauge.DirectionalTestsAverage

/-! # The actual few-links count inside one dyadic ancestor group -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem card_le_tubeCount (ρ : Measure Plane) (g p : ℕ) (E width : ℝ)
    (P₀ : Fin 2 → ℤ) (w : UnitCircle) (S : Finset (Fin 2 → ℤ))
    (hS : S ⊆ occupiedUnitCells ρ p)
    (htube : ∀ P ∈ S, dyadicCellCenter p P ∈
      directionalTube g p E width (dyadicCellCenter p P₀) w) :
    (S.card : ℝ) ≤ tubeCount ρ g p E width P₀ w := by
  calc
    _ = ∑ P ∈ S,
        {w : UnitCircle | dyadicCellCenter p P ∈
          directionalTube g p E width (dyadicCellCenter p P₀) w}.indicator (fun _ ↦ (1 : ℝ)) w := by
      calc
        _ = ∑ _P ∈ S, (1 : ℝ) := by simp
        _ = _ := by
          apply sum_congr rfl
          intro P hP
          simp only [indicator, mem_ofPred_eq, ite_eq_left (htube P hP)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hS (fun P _ _ ↦ by
      simp only [indicator, mem_ofPred_eq]
      split_ifs <;> norm_num)

/-- Precisely the occupied columns with the fixed ancestor and first source linking inequality. -/
def linkedAncestorColumns (ρ : Measure Plane) (g p : ℕ) (G : Fin 2 → ℤ)
    (c : Plane) (w₀ : UnitCircle) (τ : ℝ) : Finset (Fin 2 → ℤ) :=
  (occupiedCellDescendants ρ g p G).filter (fun P ↦
    |inner ℝ (circleQuarterTurn w₀ : Plane) (dyadicCellCenter p P - c)| ≤ τ)

theorem linkedAncestorColumns_count_le_tubeCount (ρ : Measure Plane)
    {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p) {E : ℝ}
    (hlarge : 12 ≤ (2 : ℝ) ^ (E / 2)) (G : Fin 2 → ℤ) (c : Plane) (w₀ : UnitCircle)
    {P₀ : Fin 2 → ℤ}
    (hP₀ : P₀ ∈ linkedAncestorColumns ρ g p G c w₀ (orthogonalityLinkThreshold p E))
    {w : UnitCircle} (hdir : ‖(w : Plane) - (w₀ : Plane)‖ ≤ orthogonalityArcScale a p E)
    {width : ℝ} (hwidth : 1 ≤ width) :
    ((linkedAncestorColumns ρ g p G c w₀ (orthogonalityLinkThreshold p E)).card : ℝ) ≤
      tubeCount ρ g p E width P₀ w := by
  obtain ⟨hP₀desc, hP₀link⟩ := mem_filter.mp hP₀
  have hP₀anc := (mem_filter.mp hP₀desc).2.1
  have hP₀G : dyadicCellCenter p P₀ ∈ dyadicCube g G := by
    rw [← hP₀anc]
    exact mem_dyadicCube_ancestor_of_mem hgp (dyadicCellCenter_mem p P₀)
  apply card_le_tubeCount ρ g p E width P₀ w
  · intro P hP
    obtain ⟨hP, _⟩ := mem_filter.mp hP
    obtain ⟨hPU, _, hmass⟩ := mem_filter.mp hP
    exact mem_filter.mpr ⟨hPU, hmass⟩
  · intro P hP
    obtain ⟨hPdesc, hPlink⟩ := mem_filter.mp hP
    have hPanc := (mem_filter.mp hPdesc).2.1
    apply linked_centers_mem_witness_tube hag hlarge ?_ hP₀G hPlink hP₀link hdir hwidth
    rw [← hPanc]
    exact mem_dyadicCube_ancestor_of_mem hgp (dyadicCellCenter_mem p P)

/-- The actual passing witness and Lemma 6.5 give exactly the source exponent `height+6ε`. -/
theorem linkedAncestorColumns_count_le_height (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N a g p : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ) (hag : a ≤ g) (hgp : g ≤ p) (hp : p ≤ N)
    (G : Fin 2 → ℤ) (c : Plane) (w₀ : UnitCircle) {P₀ : Fin 2 → ℤ}
    (hP₀ : P₀ ∈ linkedAncestorColumns ρ g p G c w₀
      (orthogonalityLinkThreshold p (tolerance θ N * N))) {w : UnitCircle}
    (hdir : ‖(w : Plane) - (w₀ : Plane)‖ ≤ orthogonalityArcScale a p (tolerance θ N * N))
    {width : ℝ} (hwidth : 1 ≤ width)
    (hpass : w ∈ tubePassingDirections ρ g p (tolerance θ N * N) width P₀) :
    ((linkedAncestorColumns ρ g p G c w₀
      (orthogonalityLinkThreshold p (tolerance θ N * N))).card : ℝ) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        6 * tolerance θ N)) := by
  have hE := hpar.2.2.1.1
  have hlarge : 12 ≤ (2 : ℝ) ^ ((tolerance θ N * N) / 2) := by
    calc
      _ ≤ (2 : ℝ) ^ (8 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hc := linkedAncestorColumns_count_le_tubeCount ρ hag hgp hlarge G c w₀ hP₀ hdir hwidth
  have ha := tubeAverage_le_height_of_parameterFacts ρ hρ hpar hreg hgp hp P₀
  calc
    _ ≤ _ := hc
    _ ≤ (2 : ℝ) ^ (2 * (tolerance θ N * N)) *
        (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
          4 * tolerance θ N)) :=
      hpass.trans (mul_le_mul_of_nonneg_left ha (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end FalconerThetaGauge
