module

public import FalconerThetaGauge.MaskedFourierRadialMeasure
public import FalconerThetaGauge.EqualArcCutoff
public import FalconerThetaGauge.FiniteGraphSchurIntegral

/-! # Actual square-root arc amplitudes in the finite joint Fourier measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- The actual radial and two-circle product measure, with no hypothetical energy input. -/
def maskedFourierJointMeasure (K v : ℕ) : Measure (ℝ × UnitCircle × UnitCircle) :=
  (maskedFourierRadialMeasure K v).prod (circleArcLength.prod circleArcLength)

instance isFiniteMeasure_maskedFourierJointMeasure (K v : ℕ) :
    IsFiniteMeasure (maskedFourierJointMeasure K v) := by
  unfold maskedFourierJointMeasure
  infer_instance

/-- Multiplication by the square roots of the two true smoothed arc cutoffs. -/
def maskedFourierArcPairAmplitude (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K : ℕ) (ℓ : ℝ)
    (i j : Fin (angularPartitionCount ℓ)) (z : ℝ × UnitCircle × UnitCircle) : ℂ :=
  ((Real.sqrt (equalArcCutoff K ℓ i z.2.1) *
      Real.sqrt (equalArcCutoff K ℓ j z.2.2) : ℝ) : ℂ) *
    maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
      maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2

theorem norm_maskedFourierArcPairAmplitude_sq (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin (angularPartitionCount ℓ)) (z : ℝ × UnitCircle × UnitCircle) :
    ‖maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z‖ ^ 2 =
      equalArcCutoff K ℓ i z.2.1 * equalArcCutoff K ℓ j z.2.2 *
        ‖maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 *
          maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2‖ ^ 2 := by
  simp only [maskedFourierArcPairAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (equalArcCutoff_mem_Icc K hℓ i _).1,
    Real.sq_sqrt (equalArcCutoff_mem_Icc K hℓ j _).1]
  ring

@[fun_prop]
theorem measurable_maskedFourierArcPairAmplitude (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin (angularPartitionCount ℓ)) :
    Measurable (maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j) := by
  have hi : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
      Real.sqrt (equalArcCutoff K ℓ i z.2.1)) :=
    ((measurable_equalArcCutoff K hℓ i).comp
      (measurable_fst.comp measurable_snd)).sqrt
  have hj : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
      Real.sqrt (equalArcCutoff K ℓ j z.2.2)) :=
    ((measurable_equalArcCutoff K hℓ j).comp
      (measurable_snd.comp measurable_snd)).sqrt
  have hu₁ : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
      maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1) :=
    (measurable_maskedFourierAmplitude ρ₁ X hb₁).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hu₂ : Measurable (fun z : ℝ × UnitCircle × UnitCircle ↦
      maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2) :=
    (measurable_maskedFourierAmplitude ρ₂ Y hb₂).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact ((hi.mul hj).complex_ofReal.mul hu₁).mul hu₂

theorem norm_maskedFourierArcPairAmplitude_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin (angularPartitionCount ℓ)) (z : ℝ × UnitCircle × UnitCircle) :
    ‖maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j z‖ ≤
      ρ₁.real X * ρ₂.real Y := by
  have hi : Real.sqrt (equalArcCutoff K ℓ i z.2.1) ≤ 1 :=
    Real.sqrt_le_one.mpr (equalArcCutoff_mem_Icc K hℓ i _).2
  have hj : Real.sqrt (equalArcCutoff K ℓ j z.2.2) ≤ 1 :=
    Real.sqrt_le_one.mpr (equalArcCutoff_mem_Icc K hℓ j _).2
  have hw : Real.sqrt (equalArcCutoff K ℓ i z.2.1) *
      Real.sqrt (equalArcCutoff K ℓ j z.2.2) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hi hj (Real.sqrt_nonneg _) (by norm_num)
  simp only [maskedFourierArcPairAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ 1 * ρ₁.real X * ρ₂.real Y :=
      mul_le_mul (mul_le_mul hw
        (norm_maskedFourierAmplitude_le_mass ρ₁ X hb₁ hbound₁ _ _)
        (norm_nonneg _) (by norm_num))
        (norm_maskedFourierAmplitude_le_mass ρ₂ Y hb₂ hbound₂ _ _) (norm_nonneg _)
        (by positivity)
    _ = _ := by ring

theorem memLp_maskedFourierArcPairAmplitude (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin (angularPartitionCount ℓ)) :
    MemLp (maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y b₁ b₂ K ℓ i j) 2
      (maskedFourierJointMeasure K v) :=
  MemLp.of_bound
    (measurable_maskedFourierArcPairAmplitude ρ₁ ρ₂ X Y hb₁ hb₂ K hℓ i j).aestronglyMeasurable
    (ρ₁.real X * ρ₂.real Y) (Filter.Eventually.of_forall
      (norm_maskedFourierArcPairAmplitude_le ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂ K hℓ i j))

end FalconerThetaGauge
