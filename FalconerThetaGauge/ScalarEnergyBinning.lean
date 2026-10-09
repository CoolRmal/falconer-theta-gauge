module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.Order.Interval.Finset.Basic

/-!
# Literal scalar bins in Lemma 7.3

The bins are the manuscript's half-open intervals `[jh,(j+1)h)`, indexed by
all integers. Their partition and the measure decomposition are exact,
including endpoint atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace FalconerThetaGauge

/-- The actual half-open integer bin of width `h`. -/
def scalarBin (h : ℝ) (j : ℤ) : Set ℝ := Ico ((j : ℝ) * h) ((j + 1 : ℝ) * h)

theorem measurableSet_scalarBin (h : ℝ) (j : ℤ) : MeasurableSet (scalarBin h j) :=
  measurableSet_Ico

/-- The literal bin index, with the half-open convention at atoms. -/
def scalarBinIndex (h s : ℝ) : ℤ := ⌊s / h⌋

theorem measurable_scalarBinIndex (h : ℝ) : Measurable (scalarBinIndex h) := by
  unfold scalarBinIndex
  fun_prop

theorem mem_scalarBin_index {h : ℝ} (hh : 0 < h) (s : ℝ) :
    s ∈ scalarBin h (scalarBinIndex h s) := by
  constructor
  · exact (le_div_iff₀ hh).1 (Int.floor_le (s / h))
  · exact (div_lt_iff₀ hh).1 (Int.lt_floor_add_one (s / h))

theorem iUnion_scalarBin {h : ℝ} (hh : 0 < h) : (⋃ j : ℤ, scalarBin h j) = univ := by
  apply eq_univ_iff_forall.2
  intro s
  exact mem_iUnion.2 ⟨scalarBinIndex h s, mem_scalarBin_index hh s⟩

theorem scalarBin_pairwise_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (Disjoint on scalarBin h) := by
  unfold scalarBin
  have hm : Monotone (fun j : ℤ ↦ (j : ℝ) * h) := by
    intro j k hjk
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) hh.le
  simpa only [Order.succ_eq_add_one, Int.cast_add, Int.cast_one] using
    hm.pairwise_disjoint_on_Ico_succ

/-- Every finite positive scalar measure decomposes into its actual bin restrictions. -/
theorem measure_eq_sum_scalarBin (η : Measure ℝ) {h : ℝ} (hh : 0 < h) :
    η = Measure.sum (fun j : ℤ ↦ η.restrict (scalarBin h j)) := by
  have heq := Measure.restrict_iUnion (μ := η)
    (scalarBin_pairwise_disjoint hh) (measurableSet_scalarBin h)
  rwa [iUnion_scalarBin hh, Measure.restrict_univ] at heq

/-- The literal bin mass, including any endpoint atom at the left endpoint. -/
def scalarBinMass (η : Measure ℝ) (h : ℝ) (j : ℤ) : ℝ≥0∞ := η (scalarBin h j)

/-- The squared bin mass in the binning proof. -/
def scalarBinSquareMass (η : Measure ℝ) (h : ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, scalarBinMass η h j ^ (2 : ℕ)

/-- The exact small-diagonal pair mass used by Lemma 7.3. -/
def scalarCollisionMass (η ζ : Measure ℝ) (h u : ℝ) : ℝ≥0∞ :=
  η.prod ζ {p : ℝ × ℝ | |p.1 - p.2 - u| ≤ h}

theorem measurableSet_scalarCollision (h u : ℝ) :
    MeasurableSet {p : ℝ × ℝ | |p.1 - p.2 - u| ≤ h} := by
  have hf : Continuous (fun p : ℝ × ℝ ↦ |p.1 - p.2 - u|) := by fun_prop
  exact (isClosed_le hf continuous_const).measurableSet

theorem scalarBin_difference_bounds {h s t : ℝ} {j k : ℤ}
    (hs : s ∈ scalarBin h j) (ht : t ∈ scalarBin h k) :
    (((j - k : ℤ) : ℝ) - 1) * h < s - t ∧
      s - t < (((j - k : ℤ) : ℝ) + 1) * h := by
  simp only [scalarBin, mem_Ico, Int.cast_sub] at *
  constructor <;> nlinarith

/-- The diagonal rectangles are disjoint and each lies in the true width-`h` collision set. -/
theorem scalarBinSquareMass_le_collision (η : Measure ℝ) [SFinite η]
    {h : ℝ} (hh : 0 < h) : scalarBinSquareMass η h ≤ scalarCollisionMass η η h 0 := by
  have hdisj : Pairwise (Disjoint on fun j : ℤ ↦ scalarBin h j ×ˢ scalarBin h j) := by
    intro j k hjk
    exact (scalarBin_pairwise_disjoint hh hjk).set_prod_left _ _
  have hrect : ∀ j, MeasurableSet (scalarBin h j ×ˢ scalarBin h j) :=
    fun j ↦ (measurableSet_scalarBin h j).prod (measurableSet_scalarBin h j)
  have heq : η.prod η (⋃ j : ℤ, scalarBin h j ×ˢ scalarBin h j) =
      scalarBinSquareMass η h := by
    rw [measure_iUnion hdisj hrect]
    simp only [Measure.prod_prod, scalarBinSquareMass, scalarBinMass, pow_two]
  rw [← heq]
  apply measure_mono
  intro p hp
  obtain ⟨j, hj⟩ := mem_iUnion.1 hp
  obtain ⟨hl, hu⟩ := scalarBin_difference_bounds hj.1 hj.2
  simp only [sub_self, Int.cast_zero, zero_sub, zero_add] at hl hu
  exact (abs_le.2 ⟨by linarith, by linarith⟩ : |p.1 - p.2 - 0| ≤ h)

/-- Genuine countable Cauchy--Schwarz for the nonnegative bin sequences. -/
theorem scalarBin_cauchy_schwarz (b c : ℤ → ℝ≥0∞) :
    (∑' j : ℤ, b j * c j) ≤
      (∑' j : ℤ, b j ^ (2 : ℕ)) ^ (1 / 2 : ℝ) *
        (∑' j : ℤ, c j ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ)
    Real.HolderConjugate.two_two (measurable_of_countable b).aemeasurable
      (measurable_of_countable c).aemeasurable
  simpa only [Pi.mul_apply, lintegral_count, ENNReal.rpow_two] using h

end FalconerThetaGauge
