/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.CodingConverse
import CapacityAtlasForMathlib.InformationTheory.FiniteProductDistribution
import CapacityAtlasForMathlib.InformationTheory.FiniteMixture

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {U X Y M : Type*} [Fintype U] [Fintype X] [Fintype Y]
  [Fintype M] [Nonempty M] [DecidableEq M]

/-- The input law of a uniformly chosen codeword. -/
noncomputable def codebookInput [DecidableEq X] (book : M → X) : FiniteDistribution X :=
  (FiniteDistribution.uniform M).map book

/-- Averaging the empirical input law recovers the generating distribution. -/
theorem mixture_codebookInput [DecidableEq X] (p : FiniteDistribution X) :
    FiniteDistribution.mixture
      (FiniteDistribution.productFamily (fun _ : M ↦ p))
      (fun book ↦ codebookInput book) = p := by
  classical
  ext x
  change (∑ book : M → X, (∏ m, p (book m)) *
    ∑ m with book m = x, (Fintype.card M : ℝ)⁻¹) = p x
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  have heval (m : M) :
      (∑ book : M → X, (∏ j, p (book j)) *
        if book m = x then (Fintype.card M : ℝ)⁻¹ else 0) =
      p x * (Fintype.card M : ℝ)⁻¹ := by
    simpa using FiniteProductProbability.sum_prod_mul_apply
      (fun _ a ↦ p a) (fun a ↦ if a = x then (Fintype.card M : ℝ)⁻¹ else 0)
      (fun _ ↦ p.sum_probability) m
  simp_rw [heval]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Random coding does not increase the expected information revealed to an observer. -/
theorem expected_codebook_mutualInformationBits_le [DecidableEq X]
    (W : FiniteChannel X Y) (p : FiniteDistribution X) :
    (∑ book : M → X, FiniteDistribution.productFamily (fun _ : M ↦ p) book *
      (W.encoded book).mutualInformationBits (FiniteDistribution.uniform M)) ≤
      W.mutualInformationBits p := by
  simp_rw [encoded_mutualInformationBits]
  have h := W.mutualInformationBits_mixture_ge
    (FiniteDistribution.productFamily (fun _ : M ↦ p))
    (fun book ↦ codebookInput book)
  rw [mixture_codebookInput] at h
  exact h

/-- The average random-coding error bound, retaining the ensemble for other constraints. -/
theorem expected_thresholdCode_averageErrorProbability_le
    (W : FiniteChannel X Y) (p : FiniteDistribution X) (threshold : ℝ) :
    (∑ book : M → X, FiniteDistribution.productFamily (fun _ : M ↦ p) book *
      (W.thresholdCode p threshold book).averageErrorProbability) ≤
      W.informationDensityLowerTailMass p threshold +
        (Fintype.card M : ℝ) * Real.exp (-threshold) := by
  let bound := W.informationDensityLowerTailMass p threshold +
    (Fintype.card M : ℝ) * Real.exp (-threshold)
  calc
    _ = (Fintype.card M : ℝ)⁻¹ * ∑ m : M, ∑ book : M → X,
        FiniteProductProbability.mass p book *
          (W.thresholdCode p threshold book).errorProbability m := by
      simp_rw [OneShotCode.averageErrorProbability_eq, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro m
      apply Fintype.sum_congr
      intro book
      change (∏ i, p (book i)) * (_ * _) = _ * ((∏ i, p (book i)) * _)
      ring
    _ ≤ (Fintype.card M : ℝ)⁻¹ * ∑ _m : M, bound := by
      gcongr with m
      exact W.expected_thresholdCode_errorProbability_le p threshold m
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      dsimp [bound]
      field_simp

/-- Satellite decoding averaged over the known cloud symbol. -/
theorem expected_conditional_thresholdCode_error_le
    (W : FiniteChannel X Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution X) (threshold : U → ℝ) :
    (∑ u, p u * ∑ book : M → X,
      FiniteDistribution.productFamily (fun _ : M ↦ q u) book *
        (W.thresholdCode (q u) (threshold u) book).averageErrorProbability) ≤
      ∑ u, p u * (W.informationDensityLowerTailMass (q u) (threshold u) +
        (Fintype.card M : ℝ) * Real.exp (-threshold u)) := by
  apply Finset.sum_le_sum
  intro u _
  exact mul_le_mul_of_nonneg_left
    (W.expected_thresholdCode_averageErrorProbability_le (q u) (threshold u))
    (p.nonnegative u)

/-- The same ensemble controls the information revealed by each satellite code. -/
theorem expected_conditional_codebook_mutualInformationBits_le [DecidableEq X]
    (W : FiniteChannel X Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution X) :
    (∑ u, p u * ∑ book : M → X,
      FiniteDistribution.productFamily (fun _ : M ↦ q u) book *
        (W.encoded book).mutualInformationBits (FiniteDistribution.uniform M)) ≤
      ∑ u, p u * W.mutualInformationBits (q u) := by
  apply Finset.sum_le_sum
  intro u _
  exact mul_le_mul_of_nonneg_left
    (W.expected_codebook_mutualInformationBits_le (q u)) (p.nonnegative u)

end CapacityAtlas.FiniteChannel
