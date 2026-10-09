module

public import FalconerThetaGauge.SpaceSplittingNearCells
public import FalconerThetaGauge.MaskedFourierCells
public import FalconerThetaGauge.MaskedFourierArcEnergy

/-! # Literal occupied-cell expansion and the `81²` near-row Schur bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingJointAmplitude (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (z : ℝ × UnitCircle × UnitCircle) : ℂ :=
  maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 * maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2

@[fun_prop]
theorem measurable_spaceSplittingJointAmplitude (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) :
    Measurable (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂) :=
  ((measurable_maskedFourierAmplitude ρ₁ X hb₁).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
    ((measurable_maskedFourierAmplitude ρ₂ Y hb₂).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem norm_spaceSplittingJointAmplitude_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (z : ℝ × UnitCircle × UnitCircle) :
    ‖spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z‖ ≤
      ρ₁.real X * ρ₂.real Y := by
  rw [spaceSplittingJointAmplitude, norm_mul]
  exact mul_le_mul (norm_maskedFourierAmplitude_le_mass ρ₁ X hb₁ hbound₁ _ _)
    (norm_maskedFourierAmplitude_le_mass ρ₂ Y hb₂ hbound₂ _ _) (norm_nonneg _)
    measureReal_nonneg

theorem memLp_spaceSplittingJointAmplitude (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    MemLp (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂) 2
      (maskedFourierJointMeasure K v) :=
  MemLp.of_bound
    (measurable_spaceSplittingJointAmplitude ρ₁ ρ₂ X Y hb₁ hb₂).aestronglyMeasurable
    (ρ₁.real X * ρ₂.real Y) (Filter.Eventually.of_forall
      (norm_spaceSplittingJointAmplitude_le ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂))

theorem spaceSplittingJointAmplitude_occupiedCellDescendants (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (z : ℝ × UnitCircle × UnitCircle) :
    spaceSplittingJointAmplitude ρ₁ ρ₂ (dyadicCube a X) (dyadicCube a Y) b₁ b₂ z =
      ∑ P ∈ (occupiedCellDescendants ρ₁ a p X).product
        (occupiedCellDescendants ρ₂ a p Y),
          spaceSplittingJointAmplitude ρ₁ ρ₂ (dyadicCube p P.1)
            (dyadicCube p P.2) b₁ b₂ z := by
  simp only [spaceSplittingJointAmplitude]
  rw [maskedFourierAmplitude_occupiedCellDescendants ρ₁ hρ₁ hap X hb₁ hbound₁,
    maskedFourierAmplitude_occupiedCellDescendants ρ₂ hρ₂ hap Y hb₂ hbound₂,
    product_eq_sprod, sum_product]
  simp only [sum_mul, mul_sum]
  exact sum_comm

/-- The source near terms are bounded by the true child energies with exactly `81²`. -/
theorem mass_mul_maskedFourierEnergy_le_near_schur (ρ₁ ρ₂ : Measure Plane)
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (hρ₁ : ρ₁ unitSquare = 1) (hρ₂ : ρ₂ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    let s := (occupiedCellDescendants ρ₁ a p X).product
      (occupiedCellDescendants ρ₂ a p Y)
    (ρ₁.real (dyadicCube a X) * ρ₂.real (dyadicCube a Y)) *
        maskedFourierEnergy ρ₁ ρ₂ (dyadicCube a X) (dyadicCube a Y) b₁ b₂ K v ≤
      (81 : ℝ) ^ 2 * (∑ P ∈ s,
        (ρ₁.real (dyadicCube p P.1) * ρ₂.real (dyadicCube p P.2)) *
          maskedFourierEnergy ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ K v) +
      ∑ P ∈ s, ∑ Q ∈ s, if spaceSplittingNear p P Q then 0 else
        |∫ z, inner ℝ
          (spaceSplittingJointAmplitude ρ₁ ρ₂ (dyadicCube p P.1)
            (dyadicCube p P.2) b₁ b₂ z)
          (spaceSplittingJointAmplitude ρ₁ ρ₂ (dyadicCube p Q.1)
            (dyadicCube p Q.2) b₁ b₂ z)
            ∂maskedFourierJointMeasure K v| := by
  dsimp only
  let s := (occupiedCellDescendants ρ₁ a p X).product
    (occupiedCellDescendants ρ₂ a p Y)
  let Z := fun P : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
    spaceSplittingJointAmplitude ρ₁ ρ₂ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂
  have hdegree : ∀ P ∈ s,
      ((s.filter (spaceSplittingNear p P)).card : ℝ) ≤ (81 : ℝ) ^ 2 := by
    intro P _
    exact_mod_cast spaceSplittingNear_row_card_le p s P
  have hcross : ∀ P ∈ s, ∀ Q ∈ s,
      Integrable (fun z ↦ inner ℝ (Z P z) (Z Q z)) (maskedFourierJointMeasure K v) := by
    intro P _ Q _
    exact integrable_real_inner_of_memLp_two
      (memLp_spaceSplittingJointAmplitude ρ₁ ρ₂ _ _ hb₁ hb₂ hbound₁ hbound₂ K v)
      (memLp_spaceSplittingJointAmplitude ρ₁ ρ₂ _ _ hb₁ hb₂ hbound₁ hbound₂ K v)
  have he : spaceSplittingJointAmplitude ρ₁ ρ₂ (dyadicCube a X) (dyadicCube a Y) b₁ b₂ =
      fun z ↦ ∑ P ∈ s, Z P z := by
    funext z
    exact spaceSplittingJointAmplitude_occupiedCellDescendants ρ₁ ρ₂ hρ₁ hρ₂ hap X Y
      hb₁ hb₂ hbound₁ hbound₂ z
  rw [mass_mul_maskedFourierEnergy_joint ρ₁ ρ₂ _ _ hb₁ hb₂ hbound₁ hbound₂]
  change (∫ z, ‖spaceSplittingJointAmplitude ρ₁ ρ₂ _ _ b₁ b₂ z‖ ^ 2 ∂_) ≤ _
  rw [he]
  have hh := integral_norm_sum_sq_le_graph_schur (maskedFourierJointMeasure K v) s
    (spaceSplittingNear p) (fun {_ _} h ↦ spaceSplittingNear_symm h) Z hdegree hcross
  convert hh using 2
  apply congrArg ((81 : ℝ) ^ 2 * ·)
  apply sum_congr rfl
  intro P _
  exact mass_mul_maskedFourierEnergy_joint ρ₁ ρ₂ _ _ hb₁ hb₂ hbound₁ hbound₂ K v

end FalconerThetaGauge
