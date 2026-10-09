module

public import FalconerThetaGauge.RadialProjectionSpreadRN

/-!
# Compact retained pin sets with uniform genuine radial moments

The jointly measurable actual radial moment is finite almost everywhere.
Increasing Borel good-pin sets exhaust the pin measure, so one has mass
greater than one half. Inner regularity retains a compact subset of mass
greater than one quarter on which every pin has the stated uniform bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace FalconerThetaGauge

/-- The literal radial Orlicz moment as a measurable function of the pin. -/
def radialOrliczMoment (ν : Measure Plane) [SFinite ν] (γ : ℝ) (x : Plane) : ℝ≥0∞ :=
  ∫⁻ w, orliczPhiExtended γ (radialProjectionDensity ν x w) ∂circleArcLength

@[fun_prop]
theorem measurable_radialOrliczMoment (ν : Measure Plane) [SFinite ν] (γ : ℝ) :
    Measurable (radialOrliczMoment ν γ) := by
  unfold radialOrliczMoment
  fun_prop

/-- Good pins have actual radial absolute continuity and a finite explicit moment cutoff. -/
def goodRadialPins (ν : Measure Plane) [SFinite ν] (γ : ℝ) (n : ℕ) : Set Plane :=
  {x | ν.map (radialProjection x) ≪ circleArcLength ∧ radialOrliczMoment ν γ x ≤ n}

theorem measurableSet_goodRadialPins (ν : Measure Plane) [IsFiniteMeasure ν] (γ : ℝ) (n : ℕ) :
    MeasurableSet (goodRadialPins ν γ n) := by
  exact (Kernel.measurableSet_absolutelyContinuous (radialProjectionKernel ν)
    (Kernel.const Plane circleArcLength)).inter
      (measurableSet_le (measurable_radialOrliczMoment ν γ) measurable_const)

theorem monotone_goodRadialPins (ν : Measure Plane) [SFinite ν] (γ : ℝ) :
    Monotone (goodRadialPins ν γ) := by
  intro n m hnm x hx
  exact ⟨hx.1, hx.2.trans (by exact_mod_cast hnm)⟩

/-- A Borel uniformly bounded good-pin set has more than half of the original probability. -/
theorem exists_goodRadialPins_mass_gt_half
    (μ ν : ProbabilityMeasure Plane) (γ : ℝ) {S : Set Plane}
    (hS : MeasurableSet S) (hmass : (μ : Measure Plane) S = 1)
    (hgood : ∀ᵐ x ∂(μ : Measure Plane), ν.map (radialProjection x) ≪ circleArcLength ∧
      radialOrliczMoment (ν : Measure Plane) γ x ≠ ∞) :
    ∃ n : ℕ, (1 / 2 : ℝ≥0∞) < (μ : Measure Plane) (S ∩ goodRadialPins ν γ n) := by
  let A : ℕ → Set Plane := fun n ↦ S ∩ goodRadialPins ν γ n
  have hA : ∀ n, MeasurableSet (A n) := fun n ↦ hS.inter (measurableSet_goodRadialPins ν γ n)
  have hmono : Monotone A := fun n m hnm ↦ inter_subset_inter_right S
    (monotone_goodRadialPins ν γ hnm)
  have hmem : ∀ᵐ x ∂(μ : Measure Plane), x ∈ ⋃ n, A n := by
    filter_upwards [(mem_ae_iff_prob_eq_one hS).mpr hmass, hgood] with x hxS hx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx.2
    exact mem_iUnion.mpr ⟨n, hxS, hx.1, hn.le⟩
  have hfull : (μ : Measure Plane) (⋃ n, A n) = 1 :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hA)).mp hmem
  have hlim : Tendsto (fun n ↦ (μ : Measure Plane) (A n)) atTop (𝓝 1) := by
    simpa only [hfull, Function.comp_def] using
      tendsto_measure_iUnion_atTop (μ := (μ : Measure Plane)) hmono
  exact (hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ≥0∞) < 1))).exists

/-- A genuine compact quarter-mass pin carrier has a bound at every one of its points. -/
theorem exists_compact_goodRadialPins
    (μ ν : ProbabilityMeasure Plane) (γ : ℝ) {S : Set Plane}
    (hS : IsCompact S) (hmass : (μ : Measure Plane) S = 1)
    (hgood : ∀ᵐ x ∂(μ : Measure Plane), ν.map (radialProjection x) ≪ circleArcLength ∧
      radialOrliczMoment (ν : Measure Plane) γ x ≠ ∞) :
    ∃ (n : ℕ) (A : Set Plane), IsCompact A ∧ A ⊆ S ∧
      (1 / 4 : ℝ≥0∞) < (μ : Measure Plane) A ∧
      ∀ x ∈ A, ν.map (radialProjection x) ≪ circleArcLength ∧
        radialOrliczMoment (ν : Measure Plane) γ x ≤ n := by
  obtain ⟨n, hn⟩ := exists_goodRadialPins_mass_gt_half μ ν γ hS.measurableSet hmass hgood
  obtain ⟨A, hAsub, hA, hμA⟩ :=
    (hS.measurableSet.inter (measurableSet_goodRadialPins ν γ n)).exists_lt_isCompact
      ((by norm_num : (1 / 4 : ℝ≥0∞) < 1 / 2).trans hn)
  exact ⟨n, A, hA, hAsub.trans inter_subset_left, hμA, fun x hx ↦ (hAsub hx).2⟩

end FalconerThetaGauge
