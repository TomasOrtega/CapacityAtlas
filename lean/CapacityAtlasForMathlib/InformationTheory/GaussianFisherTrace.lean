/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianFisherConvolution

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable def traceFisherWith (reference : Measure (EuclideanSpace ℝ ι))
    (density : EuclideanSpace ℝ ι → ℝ) : ℝ :=
  ∑ i, directionalFisherWith reference density (EuclideanSpace.single i 1)

lemma traceFisherWith_nonneg (reference : Measure (EuclideanSpace ℝ ι))
    (density : EuclideanSpace ℝ ι → ℝ) (hpos : ∀ x, 0 ≤ density x) :
    0 ≤ traceFisherWith reference density :=
  Finset.sum_nonneg (fun _ _ ↦ directionalFisherWith_nonneg reference density _ hpos)

lemma quadratic_inv_smul_one_single {t : ℝ} (ht : 0 < t) (i : ι) :
    (EuclideanSpace.single i 1 : EuclideanSpace ℝ ι) ⬝ᵥ
      (t • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ (EuclideanSpace.single i 1 : EuclideanSpace ℝ ι) = 1 / t := by
  letI : Invertible t := invertibleOfNonzero ht.ne'
  rw [Matrix.inv_smul (A := (1 : Matrix ι ι ℝ)) t (by simp)]
  simp [invOf_eq_inv, PiLp.ofLp_single]

lemma traceFisherWith_gaussianMixture_add_isotropic_le
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    {t : ℝ} (ht : 0 < t) (u : ℝ) :
    traceFisherWith volume (gaussianMixturePDFReal w m (N + t • (1 : Matrix ι ι ℝ))) ≤
      u ^ 2 * traceFisherWith volume (gaussianMixturePDFReal w m N) +
        (1 - u) ^ 2 * ((Fintype.card ι : ℝ) / t) := by
  have hi (i : ι) := directionalFisherWith_gaussianMixture_add_le w hw hw1 m 0
    (EuclideanSpace.single i 1) N (t • (1 : Matrix ι ι ℝ)) hN (Matrix.PosDef.one.smul ht) u
  simp only [add_zero, quadratic_inv_smul_one_single ht] at hi
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
  apply h.trans_eq
  simp only [traceFisherWith, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The optimized trace Fisher contraction under isotropic Gaussian convolution. -/
theorem traceFisherWith_gaussianMixture_add_isotropic_le_optimized
    [Nonempty ι] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    {t : ℝ} (ht : 0 < t) :
    traceFisherWith volume (gaussianMixturePDFReal w m (N + t • (1 : Matrix ι ι ℝ))) ≤
      (Fintype.card ι : ℝ) * traceFisherWith volume (gaussianMixturePDFReal w m N) /
        ((Fintype.card ι : ℝ) + t * traceFisherWith volume (gaussianMixturePDFReal w m N)) := by
  let d : ℝ := Fintype.card ι
  let J := traceFisherWith volume (gaussianMixturePDFReal w m N)
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  have hJ : 0 ≤ J := traceFisherWith_nonneg volume _
    (fun x ↦ (gaussianMixturePDFReal_pos w hw hw1 m N hN x).le)
  have hden : d + t * J ≠ 0 := (add_pos_of_pos_of_nonneg hd (mul_nonneg ht.le hJ)).ne'
  have h := traceFisherWith_gaussianMixture_add_isotropic_le w hw hw1 m N hN ht (d / (d + t * J))
  convert! h using 1
  change d * J / (d + t * J) = (d / (d + t * J)) ^ 2 * J +
    (1 - d / (d + t * J)) ^ 2 * (d / t)
  field_simp
  ring

end CapacityAtlas.MeasureInformation
