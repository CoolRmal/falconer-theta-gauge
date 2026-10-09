module

public import FalconerThetaGauge.OrthogonalitySecondLinks
public import FalconerThetaGauge.FiniteFiberCount

/-! # The genuine first-column count across all dyadic ancestor groups -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def activeLinkedFirstColumns (ρ : Measure Plane) (a g p : ℕ) (X : Fin 2 → ℤ)
    (E width : ℝ) (c : Plane) (w₀ : UnitCircle) : Finset (Fin 2 → ℤ) :=
  (occupiedCellDescendants ρ a p X).filter (fun P ↦
    |inner ℝ (circleQuarterTurn w₀ : Plane) (dyadicCellCenter p P - c)| ≤
      orthogonalityLinkThreshold p E ∧ ∃ w : UnitCircle,
      ‖(w : Plane) - (w₀ : Plane)‖ ≤ orthogonalityArcScale a p E ∧
      w ∈ tubePassingDirections ρ g p E width P)

theorem activeLinkedFirstColumns_fiber_count_le (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N a g p : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ) (hag : a ≤ g) (hgp : g ≤ p) (hp : p ≤ N)
    (X : Fin 2 → ℤ) (c : Plane) (w₀ : UnitCircle) {width : ℝ} (hwidth : 1 ≤ width)
    (G : Fin 2 → ℤ) :
    (((activeLinkedFirstColumns ρ a g p X (tolerance θ N * N) width c w₀).filter
      (fun P ↦ ancestor (p - g) P = G)).card : ℝ) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        6 * tolerance θ N)) := by
  let F := (activeLinkedFirstColumns ρ a g p X (tolerance θ N * N) width c w₀).filter
    (fun P ↦ ancestor (p - g) P = G)
  by_cases hF : F.Nonempty
  · obtain ⟨P₀, hP₀⟩ := hF
    obtain ⟨hP₀S, hP₀anc⟩ := mem_filter.mp hP₀
    obtain ⟨hP₀desc, hP₀link, w, hdir, hpass⟩ := mem_filter.mp hP₀S
    have hsub : F ⊆ linkedAncestorColumns ρ g p G c w₀
        (orthogonalityLinkThreshold p (tolerance θ N * N)) := by
      intro P hP
      obtain ⟨hPS, hPanc⟩ := mem_filter.mp hP
      obtain ⟨hPdesc, hPlink, _⟩ := mem_filter.mp hPS
      obtain ⟨hPU, _, hmass⟩ := mem_filter.mp hPdesc
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hPU, hPanc, hmass⟩, hPlink⟩
    have hP₀G := hsub hP₀
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (linkedAncestorColumns_count_le_height ρ hρ hpar hreg hag hgp hp G c w₀
        hP₀G hdir hwidth hpass)
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

theorem activeLinkedFirstColumns_count_le (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {θ : ℝ} {N a g p : ℕ} (hpar : ParameterFacts θ N)
    (hreg : IsRegularThrough (tolerance θ N) N ρ) (hag : a ≤ g) (hgp : g ≤ p) (hp : p ≤ N)
    (hgap : (g : ℝ) - a ≤ tolerance θ N * N)
    (X : Fin 2 → ℤ) (c : Plane) (w₀ : UnitCircle) {width : ℝ} (hwidth : 1 ≤ width) :
    ((activeLinkedFirstColumns ρ a g p X (tolerance θ N * N) width c w₀).card : ℝ) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        8 * tolerance θ N)) := by
  let S := activeLinkedFirstColumns ρ a g p X (tolerance θ N * N) width c w₀
  let H := S.image (ancestor (p - g))
  have hgroups : H.card ≤ 4 ^ (g - a) := by
    apply card_image_ancestor_le S (p - g) (g - a) X
    intro P hP
    have he : p - g + (g - a) = p - a := by omega
    rw [he]
    exact (mem_filter.mp (mem_filter.mp hP).1).2.1
  have hpower : ((4 : ℝ) ^ (g - a)) ≤ (2 : ℝ) ^ (2 * (tolerance θ N * N)) := by
    calc
      _ = (4 : ℝ) ^ ((g - a : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = (2 : ℝ) ^ (2 * ((g - a : ℕ) : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
        norm_num
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [Nat.cast_sub hag]
        linarith
  have hH₀ : (H.card : ℝ) ≤ (4 : ℝ) ^ (g - a) := by exact_mod_cast hgroups
  have hH : (H.card : ℝ) ≤ (2 : ℝ) ^ (2 * (tolerance θ N * N)) := hH₀.trans hpower
  have hf (G : Fin 2 → ℤ) : ((S.filter (fun P ↦ ancestor (p - g) P = G)).card : ℝ) ≤
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        6 * tolerance θ N)) :=
    activeLinkedFirstColumns_fiber_count_le ρ hρ hpar hreg hag hgp hp X c w₀ hwidth G
  have hc : (S.card : ℝ) ≤ (H.card : ℝ) *
      (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
        6 * tolerance θ N)) := by
    apply finite_fiber_count_le_mul S H (ancestor (p - g))
    · exact fun P hP ↦ mem_image_of_mem _ hP
    · intro G _
      convert hf G using 1
      congr 2
      ext P
      simp only [mem_filter]
  calc
    _ ≤ _ := hc
    _ ≤ (2 : ℝ) ^ (2 * (tolerance θ N * N)) *
        (2 : ℝ) ^ (N * (profileHeight (regularMeasureExcess ρ N) p g p +
          6 * tolerance θ N)) := mul_le_mul_of_nonneg_right hH (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end FalconerThetaGauge
