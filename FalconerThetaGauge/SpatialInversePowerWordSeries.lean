/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpatialInversePowerBinomial
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! # Expanding the genuine binomial series into separated finite words -/

@[expose] public section

noncomputable section

open Finset

namespace FalconerThetaGauge

abbrev SpatialSeparationAtom := Fin 2 × Fin 5

/-- Each binomial power expands into its finite words in the ten spatial monomials. -/
abbrev SpatialSeparationWord := Σ m : ℕ, Fin m → SpatialSeparationAtom

def spatialSeparationWordCoefficient (j : ℕ) (D : ℝ)
    (a : SpatialSeparationAtom → ℝ) (w : SpatialSeparationWord) : ℝ :=
  D⁻¹ ^ j * Ring.choose (-(j : ℝ) / 2) w.1 * ∏ r, a (w.2 r)

theorem sum_spatialSeparationWordCoefficient_abs (j m : ℕ) {D : ℝ} (hD : 0 < D)
    (a : SpatialSeparationAtom → ℝ) :
    (∑ w : Fin m → SpatialSeparationAtom,
      |spatialSeparationWordCoefficient j D a ⟨m, w⟩|) =
      D⁻¹ ^ j * (|Ring.choose (-(j : ℝ) / 2) m| * (∑ k, |a k|) ^ m) := by
  simp only [spatialSeparationWordCoefficient, abs_mul, abs_pow, abs_inv,
    abs_of_pos hD, Finset.abs_prod]
  rw [← mul_sum, ← Fintype.sum_pow (fun k : SpatialSeparationAtom ↦ |a k|) m]
  ring

theorem summable_spatialSeparationWordCoefficient_abs (j : ℕ) {D : ℝ} (hD : 0 < D)
    {a : SpatialSeparationAtom → ℝ} (ha : (∑ k, |a k|) ≤ 1 / 4) :
    Summable (fun w ↦ |spatialSeparationWordCoefficient j D a w|) := by
  apply (summable_sigma_of_nonneg (fun _ ↦ abs_nonneg _)).mpr
  refine ⟨fun _ ↦ Summable.of_finite, ?_⟩
  simp_rw [tsum_fintype, sum_spatialSeparationWordCoefficient_abs j _ hD]
  have hs := summable_inversePowerBinomial_abs j (sum_nonneg (fun _ _ ↦ abs_nonneg _)) ha
  exact hs.mul_left _

theorem tsum_spatialSeparationWordCoefficient_abs_le (j : ℕ) {D : ℝ} (hD : 0 < D)
    {a : SpatialSeparationAtom → ℝ} (ha : (∑ k, |a k|) ≤ 1 / 4) :
    (∑' w, |spatialSeparationWordCoefficient j D a w|) ≤ 2 * (2 / D) ^ j := by
  have hs := summable_spatialSeparationWordCoefficient_abs j hD ha
  rw [hs.tsum_sigma]
  simp_rw [tsum_fintype, sum_spatialSeparationWordCoefficient_abs j _ hD]
  rw [tsum_mul_left]
  calc
    _ ≤ D⁻¹ ^ j * (2 * (2 : ℝ) ^ j) := mul_le_mul_of_nonneg_left
      (tsum_inversePowerBinomial_abs_le j (sum_nonneg (fun _ _ ↦ abs_nonneg _)) ha)
      (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

def spatialSeparationWordTerm (j : ℕ) (D : ℝ) (a f g : SpatialSeparationAtom → ℝ)
    (w : SpatialSeparationWord) : ℝ :=
  spatialSeparationWordCoefficient j D a w * (∏ r, f (w.2 r)) * ∏ r, g (w.2 r)

theorem norm_spatialSeparationWordTerm_le (j : ℕ) (D : ℝ)
    (a f g : SpatialSeparationAtom → ℝ) (hf : ∀ k, |f k| ≤ 1) (hg : ∀ k, |g k| ≤ 1)
    (w : SpatialSeparationWord) :
    ‖spatialSeparationWordTerm j D a f g w‖ ≤
      |spatialSeparationWordCoefficient j D a w| := by
  rw [spatialSeparationWordTerm, Real.norm_eq_abs, abs_mul, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  have hfp : (∏ r : Fin w.1, |f (w.2 r)|) ≤ 1 :=
    prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ hf _)
  have hgp : (∏ r : Fin w.1, |g (w.2 r)|) ≤ 1 :=
    prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ hg _)
  calc
    _ ≤ |spatialSeparationWordCoefficient j D a w| * 1 * 1 := by gcongr
    _ = _ := by ring

theorem sum_spatialSeparationWordTerm (j m : ℕ) (D : ℝ)
    (a f g : SpatialSeparationAtom → ℝ) :
    (∑ w : Fin m → SpatialSeparationAtom, spatialSeparationWordTerm j D a f g ⟨m, w⟩) =
      D⁻¹ ^ j * (Ring.choose (-(j : ℝ) / 2) m * (∑ k, a k * f k * g k) ^ m) := by
  rw [Fintype.sum_pow]
  simp only [mul_sum]
  apply sum_congr rfl
  intro w _
  rw [spatialSeparationWordTerm, spatialSeparationWordCoefficient]
  simp only [prod_mul_distrib]
  ring

theorem hasSum_spatialSeparationWordTerm (j : ℕ) {D : ℝ} (hD : 0 < D)
    {a : SpatialSeparationAtom → ℝ} (ha : (∑ k, |a k|) ≤ 1 / 4)
    (f g : SpatialSeparationAtom → ℝ) (hf : ∀ k, |f k| ≤ 1) (hg : ∀ k, |g k| ≤ 1) :
    HasSum (spatialSeparationWordTerm j D a f g)
      (D⁻¹ ^ j * (1 + ∑ k, a k * f k * g k) ^ (-(j : ℝ) / 2)) := by
  have hs : |∑ k, a k * f k * g k| < 1 := by
    calc
      _ ≤ ∑ k, |a k * f k * g k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |a k| := by
        apply sum_le_sum
        intro k _
        rw [abs_mul, abs_mul]
        calc
          _ ≤ |a k| * 1 * 1 := by gcongr; exact hf k; exact hg k
          _ = _ := by ring
      _ ≤ 1 / 4 := ha
      _ < 1 := by norm_num
  have hsum : Summable (spatialSeparationWordTerm j D a f g) :=
    (summable_spatialSeparationWordCoefficient_abs j hD ha).of_norm_bounded
      (norm_spatialSeparationWordTerm_le j D a f g hf hg)
  apply HasSum.sigma_of_hasSum
    ((hasSum_inversePowerBinomial j hs).mul_left (D⁻¹ ^ j)) _ hsum
  intro m
  simpa only [tsum_fintype, sum_spatialSeparationWordTerm] using
    (Summable.of_finite (L := SummationFilter.unconditional _)
      (f := fun w : Fin m → SpatialSeparationAtom ↦
      spatialSeparationWordTerm j D a f g ⟨m, w⟩)).hasSum

end FalconerThetaGauge
