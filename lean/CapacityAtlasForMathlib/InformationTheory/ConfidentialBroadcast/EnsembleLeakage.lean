/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.SeedInformation

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

theorem uniform_prod_joint {S L : Type*} [Fintype S] [Fintype L]
    [Nonempty S] [Nonempty L] :
    uniform (S × L) = (uniform S).joint (fun _ ↦ uniform L) := by
  ext a
  simp only [uniform_apply, joint_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

end CapacityAtlas.FiniteDistribution

namespace CapacityAtlas.ConfidentialBroadcast

variable {V Y S L : Type*} [Fintype V] [Fintype Y] [Fintype S] [Fintype L]
  [Nonempty S] [Nonempty L] [DecidableEq S] [DecidableEq L]

noncomputable def seedError (W : FiniteChannel V Y) (q : FiniteDistribution V)
    (threshold : ℝ) (book : S × L → V) : ℝ :=
  ∑ s, FiniteDistribution.uniform S s *
    (W.thresholdCode q threshold (fun l ↦ book (s, l))).averageErrorProbability

theorem expected_seedError_le (W : FiniteChannel V Y) (q : FiniteDistribution V)
    (threshold : ℝ) :
    (∑ book : S × L → V, FiniteDistribution.productFamily (fun _ : S × L ↦ q) book *
      seedError W q threshold book) ≤
      W.informationDensityLowerTailMass q threshold +
        (Fintype.card L : ℝ) * Real.exp (-threshold) := by
  classical
  let bound := W.informationDensityLowerTailMass q threshold +
    (Fintype.card L : ℝ) * Real.exp (-threshold)
  simp only [seedError, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s, FiniteDistribution.uniform S s *
        ∑ row : L → V, FiniteDistribution.productFamily (fun _ : L ↦ q) row *
          (W.thresholdCode q threshold row).averageErrorProbability := by
      apply Fintype.sum_congr
      intro s
      calc
        _ = FiniteDistribution.uniform S s *
            ∑ book : S × L → V, FiniteDistribution.productFamily (fun _ : S × L ↦ q) book *
              (W.thresholdCode q threshold (fun l ↦ book (s, l))).averageErrorProbability := by
          rw [Finset.mul_sum]
          apply Fintype.sum_congr
          intro book
          ring
        _ = _ := congrArg (fun x ↦ FiniteDistribution.uniform S s * x)
          (FiniteDistribution.expected_product_codebook_row q s
            (fun row : L → V ↦ (W.thresholdCode q threshold row).averageErrorProbability))
    _ ≤ ∑ s, FiniteDistribution.uniform S s * bound := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (W.expected_thresholdCode_averageErrorProbability_le q threshold)
        ((FiniteDistribution.uniform S).nonnegative s)
    _ = _ := by rw [← Finset.sum_mul, FiniteDistribution.sum_probability_eq_one, one_mul]

omit [DecidableEq S] in
theorem seed_averaging_leakage_le (W : FiniteChannel V Y) (q : FiniteDistribution V)
    (threshold : ℝ) (book : S × L → V) :
    ((W.encoded book).averageSeed (fun _ ↦ FiniteDistribution.uniform L)).mutualInformationBits
      (FiniteDistribution.uniform S) ≤
      (W.encoded book).mutualInformationBits (FiniteDistribution.uniform (S × L)) -
        Real.log (Fintype.card L) / Real.log 2 + 1 +
      seedError W q threshold book * (Real.log (Fintype.card L) / Real.log 2) := by
  have h := (W.encoded book).averageSeed_information_le (FiniteDistribution.uniform S)
    (fun s ↦ W.thresholdDecoder q threshold (fun l ↦ book (s, l)))
  rw [← FiniteDistribution.uniform_prod_joint] at h
  have henc (s : S) :
      (W.encoded book).encoded (fun l ↦ (s, l)) = W.encoded (fun l ↦ book (s, l)) := rfl
  simp_rw [henc, FiniteChannel.uniformDecoderError_encoded] at h
  exact h

/-- Weak secrecy follows by filling each confidential-message subcode near its observer capacity. -/
theorem expected_seed_averaging_leakage_le [DecidableEq V]
    (W : FiniteChannel V Y) (q : FiniteDistribution V) (threshold : ℝ) :
    (∑ book : S × L → V, FiniteDistribution.productFamily (fun _ : S × L ↦ q) book *
      ((W.encoded book).averageSeed (fun _ ↦ FiniteDistribution.uniform L)).mutualInformationBits
        (FiniteDistribution.uniform S)) ≤
      W.mutualInformationBits q - Real.log (Fintype.card L) / Real.log 2 + 1 +
      (W.informationDensityLowerTailMass q threshold +
        (Fintype.card L : ℝ) * Real.exp (-threshold)) *
        (Real.log (Fintype.card L) / Real.log 2) := by
  let books := FiniteDistribution.productFamily (fun _ : S × L ↦ q)
  let h := Real.log (Fintype.card L) / Real.log 2
  have hh : 0 ≤ h := by
    apply div_nonneg (Real.log_nonneg _) (Real.log_nonneg (by norm_num))
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty L)
  calc
    _ ≤ ∑ book, books book *
        ((W.encoded book).mutualInformationBits (FiniteDistribution.uniform (S × L)) - h + 1 +
          seedError W q threshold book * h) := by
      apply Finset.sum_le_sum
      intro book _
      exact mul_le_mul_of_nonneg_left (seed_averaging_leakage_le W q threshold book)
        (books.nonnegative book)
    _ = (∑ book, books book *
        (W.encoded book).mutualInformationBits (FiniteDistribution.uniform (S × L))) - h + 1 +
        (∑ book, books book * seedError W q threshold book) * h := by
      simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← mul_assoc, ← Finset.sum_mul, FiniteDistribution.sum_probability_eq_one, one_mul]
    _ ≤ _ := by
      gcongr
      · exact W.expected_codebook_mutualInformationBits_le q
      · exact expected_seedError_le W q threshold

theorem expected_superposition_leakage_le {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (threshold : U → ℝ) (c : C) :
    (∑ book, superpositionEnsemble (C := C) (S := S × L) p q book *
      ((W.encoded (book.2 c)).averageSeed (fun _ ↦ FiniteDistribution.uniform L)).mutualInformationBits
        (FiniteDistribution.uniform S)) ≤
      (∑ u, p u * W.mutualInformationBits (q u)) - Real.log (Fintype.card L) / Real.log 2 + 1 +
      (∑ u, p u * (W.informationDensityLowerTailMass (q u) (threshold u) +
        (Fintype.card L : ℝ) * Real.exp (-threshold u))) *
        (Real.log (Fintype.card L) / Real.log 2) := by
  classical
  let h := Real.log (Fintype.card L) / Real.log 2
  simp only [superpositionEnsemble, FiniteDistribution.joint_apply,
    Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
  calc
    _ = ∑ cloud, FiniteDistribution.productFamily (fun _ : C ↦ p) cloud *
        ∑ row : S × L → V, FiniteDistribution.productFamily (fun _ : S × L ↦ q (cloud c)) row *
          ((W.encoded row).averageSeed (fun _ ↦ FiniteDistribution.uniform L)).mutualInformationBits
            (FiniteDistribution.uniform S) := by
      apply Fintype.sum_congr
      intro cloud
      congr 1
      exact FiniteDistribution.sum_productFamily_mul_eval
        (fun j : C ↦ FiniteDistribution.productFamily (fun _ : S × L ↦ q (cloud j)))
        (fun row : S × L → V ↦
          ((W.encoded row).averageSeed (fun _ ↦ FiniteDistribution.uniform L)).mutualInformationBits
            (FiniteDistribution.uniform S)) c
    _ ≤ ∑ cloud, FiniteDistribution.productFamily (fun _ : C ↦ p) cloud *
        (W.mutualInformationBits (q (cloud c)) - h + 1 +
          (W.informationDensityLowerTailMass (q (cloud c)) (threshold (cloud c)) +
            (Fintype.card L : ℝ) * Real.exp (-threshold (cloud c))) * h) := by
      apply Finset.sum_le_sum
      intro cloud _
      exact mul_le_mul_of_nonneg_left
        (expected_seed_averaging_leakage_le W (q (cloud c)) (threshold (cloud c)))
        (FiniteDistribution.probability_nonnegative _ _)
    _ = ∑ u, p u * (W.mutualInformationBits (q u) - h + 1 +
        (W.informationDensityLowerTailMass (q u) (threshold u) +
          (Fintype.card L : ℝ) * Real.exp (-threshold u)) * h) :=
      FiniteDistribution.sum_productFamily_mul_eval (fun _ : C ↦ p)
        (fun u ↦ W.mutualInformationBits (q u) - h + 1 +
          (W.informationDensityLowerTailMass (q u) (threshold u) +
            (Fintype.card L : ℝ) * Real.exp (-threshold u)) * h) c
    _ = _ := by
      simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← mul_assoc, ← Finset.sum_mul, FiniteDistribution.sum_probability_eq_one, one_mul, h]

end CapacityAtlas.ConfidentialBroadcast
