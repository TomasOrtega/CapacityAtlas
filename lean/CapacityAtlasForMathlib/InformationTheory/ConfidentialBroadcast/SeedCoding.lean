/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.ConditionalDensity

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {S L V : Type*} [Fintype S] [Fintype L] [Fintype V]
  [DecidableEq S] [DecidableEq L]

/-- A subcode for a fixed message remains an independent random codebook. -/
theorem expected_product_codebook_row (p : FiniteDistribution V) (s : S)
    (f : (L → V) → ℝ) :
    (∑ book : S × L → V, productFamily (fun _ : S × L ↦ p) book *
      f (fun l ↦ book (s, l))) =
      ∑ row : L → V, productFamily (fun _ : L ↦ p) row * f row := by
  calc
    _ = ∑ book : S → L → V,
        productFamily (fun _ : S ↦ productFamily (fun _ : L ↦ p)) book * f (book s) := by
      apply Fintype.sum_equiv (Equiv.curry S L V)
      intro book
      simp only [productFamily_apply, Fintype.prod_prod_type]
      rfl
    _ = _ := sum_productFamily_mul_eval
      (fun _ : S ↦ productFamily (fun _ : L ↦ p)) f s

end CapacityAtlas.FiniteDistribution

namespace CapacityAtlas.ConfidentialBroadcast

variable {U V Y C S L : Type*} [Fintype U] [Fintype V] [Fintype Y]
  [Fintype C] [Fintype S] [Fintype L]
  [DecidableEq C] [DecidableEq S] [DecidableEq L]

/-- The seed can be decoded in the eavesdropper analysis when both messages are supplied. -/
theorem expected_seed_error_le [Nonempty L]
    (W : FiniteChannel V Y) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (threshold : U → ℝ) (c : C) (s : S) (l : L) :
    (∑ book, superpositionEnsemble (C := C) (S := S × L) p q book *
      (W.thresholdCode (q (book.1 c)) (threshold (book.1 c))
        (fun k ↦ book.2 c (s, k))).errorProbability l) ≤
      ∑ u, p u * (W.informationDensityLowerTailMass (q u) (threshold u) +
        (Fintype.card L : ℝ) * Real.exp (-threshold u)) := by
  classical
  simp only [superpositionEnsemble, FiniteDistribution.joint_apply,
    Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
  calc
    _ = ∑ cloud, FiniteDistribution.productFamily (fun _ : C ↦ p) cloud *
        ∑ row : L → V, FiniteDistribution.productFamily (fun _ : L ↦ q (cloud c)) row *
          (W.thresholdCode (q (cloud c)) (threshold (cloud c)) row).errorProbability l := by
      apply Fintype.sum_congr
      intro cloud
      congr 1
      rw [FiniteDistribution.sum_productFamily_mul_eval
        (fun j : C ↦ FiniteDistribution.productFamily (fun _ : S × L ↦ q (cloud j)))
        (fun row : S × L → V ↦
          (W.thresholdCode (q (cloud c)) (threshold (cloud c))
            (fun k ↦ row (s, k))).errorProbability l) c]
      exact FiniteDistribution.expected_product_codebook_row (q (cloud c)) s
        (fun row : L → V ↦
          (W.thresholdCode (q (cloud c)) (threshold (cloud c)) row).errorProbability l)
    _ ≤ ∑ cloud, FiniteDistribution.productFamily (fun _ : C ↦ p) cloud *
        (W.informationDensityLowerTailMass (q (cloud c)) (threshold (cloud c)) +
          (Fintype.card L : ℝ) * Real.exp (-threshold (cloud c))) := by
      apply Finset.sum_le_sum
      intro cloud _
      apply mul_le_mul_of_nonneg_left _ (FiniteDistribution.probability_nonnegative _ _)
      exact W.expected_thresholdCode_errorProbability_le (q (cloud c)) (threshold (cloud c)) l
    _ = _ := FiniteDistribution.sum_productFamily_mul_eval (fun _ : C ↦ p)
      (fun u ↦ W.informationDensityLowerTailMass (q u) (threshold u) +
        (Fintype.card L : ℝ) * Real.exp (-threshold u)) c

end CapacityAtlas.ConfidentialBroadcast
