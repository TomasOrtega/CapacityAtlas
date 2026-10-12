/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.EnsembleLeakage
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Prefixing

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast

variable {U V Y C S L : Type*} [Fintype U] [Fintype V] [Fintype Y]
  [Fintype C] [Fintype S] [Fintype L]
  [DecidableEq C] [DecidableEq S] [DecidableEq L]

def conditionalProduct (q : U → FiniteDistribution V) (n : ℕ) (u : Fin n → U) :
    FiniteDistribution (Fin n → V) :=
  FiniteDistribution.productFamily fun i ↦ q (u i)

theorem conditionalProduct_channel (q : U → FiniteDistribution V) (n : ℕ) :
    FiniteChannel.ofRows (conditionalProduct q n) = (FiniteChannel.ofRows q).block n := by
  ext u v
  rfl

noncomputable def densityThreshold (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (n : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * conditionalMean W p q - (n : ℝ) * δ

noncomputable def conditionalCodingBound (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (n messages : ℕ) (δ : ℝ) : ℝ :=
  ((n : ℝ) * conditionalVariance W p q) / (((n : ℝ) * δ) ^ 2) +
    (messages : ℝ) * Real.exp (-densityThreshold W p q n δ)

theorem conditionalCodingBound_nonnegative (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n messages : ℕ) (δ : ℝ) :
    0 ≤ conditionalCodingBound W p q n messages δ := by
  unfold conditionalCodingBound
  have := conditionalVariance_nonnegative W p q
  positivity

theorem expected_conditional_block_information_le (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n : ℕ) :
    (∑ u : Fin n → U, p.iid n u * (W.block n).mutualInformationBits (conditionalProduct q n u)) ≤
      (n : ℝ) * (conditionalMean W p q / Real.log 2) := by
  classical
  calc
    _ ≤ ∑ u : Fin n → U, p.iid n u * ∑ i, W.mutualInformationBits (q (u i)) := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left
        (W.block_mutualInformationBits_productFamily_le n (fun i ↦ q (u i)))
        ((p.iid n).nonnegative u)
    _ = ∑ i : Fin n, ∑ u : Fin n → U, p.iid n u * W.mutualInformationBits (q (u i)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _i : Fin n, ∑ u, p u * W.mutualInformationBits (q u) := by
      apply Fintype.sum_congr
      intro i
      exact FiniteProductProbability.sum_mass_mul_apply p
        (fun u ↦ W.mutualInformationBits (q u)) p.sum_probability i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        conditionalMean, FiniteChannel.mutualInformationBits, Finset.sum_div, mul_div_assoc]

theorem conditional_block_packing_le (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (messages : ℕ) :
    (∑ u : Fin n → U, p.iid n u *
      ((W.block n).informationDensityLowerTailMass (conditionalProduct q n u)
        (densityThreshold W p q n δ) +
        (messages : ℝ) * Real.exp (-densityThreshold W p q n δ))) ≤
      conditionalCodingBound W p q n messages δ := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    FiniteDistribution.sum_probability_eq_one, one_mul]
  exact add_le_add (conditionalLowerTail_le W p q hn hδ) le_rfl

theorem expected_block_satellite_error_le [Nonempty S]
    (W : FiniteChannel V Y) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (c : C) (s : S) :
    (∑ book, superpositionEnsemble (C := C) (S := S) (p.iid n) (conditionalProduct q n) book *
      ((W.block n).thresholdCode (conditionalProduct q n (book.1 c))
        (densityThreshold W p q n δ) (book.2 c)).errorProbability s) ≤
      conditionalCodingBound W p q n (Fintype.card S) δ :=
  (expected_satellite_error_le (W.block n) (p.iid n) (conditionalProduct q n)
    (fun _ ↦ densityThreshold W p q n δ) c s).trans
      (conditional_block_packing_le W p q hn hδ (Fintype.card S))

theorem expected_block_seed_error_le [Nonempty L]
    (W : FiniteChannel V Y) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (c : C) (s : S) (l : L) :
    (∑ book, superpositionEnsemble (C := C) (S := S × L) (p.iid n) (conditionalProduct q n) book *
      ((W.block n).thresholdCode (conditionalProduct q n (book.1 c))
        (densityThreshold W p q n δ) (fun k ↦ book.2 c (s, k))).errorProbability l) ≤
      conditionalCodingBound W p q n (Fintype.card L) δ :=
  (expected_seed_error_le (W.block n) (p.iid n) (conditionalProduct q n)
    (fun _ ↦ densityThreshold W p q n δ) c s l).trans
      (conditional_block_packing_le W p q hn hδ (Fintype.card L))

theorem expected_block_leakage_le [Nonempty S] [Nonempty L]
    (W : FiniteChannel V Y) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (c : C) :
    (∑ book, superpositionEnsemble (C := C) (S := S × L) (p.iid n) (conditionalProduct q n) book *
      (((W.block n).encoded (book.2 c)).averageSeed
        (fun _ ↦ FiniteDistribution.uniform L)).mutualInformationBits
        (FiniteDistribution.uniform S)) ≤
      (n : ℝ) * (conditionalMean W p q / Real.log 2) -
        Real.log (Fintype.card L) / Real.log 2 + 1 +
      conditionalCodingBound W p q n (Fintype.card L) δ *
        (Real.log (Fintype.card L) / Real.log 2) := by
  have hlog : 0 ≤ Real.log (Fintype.card L) / Real.log 2 := by
    apply div_nonneg (Real.log_nonneg _) (Real.log_nonneg (by norm_num))
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty L)
  apply (expected_superposition_leakage_le (W.block n) (p.iid n) (conditionalProduct q n)
    (fun _ ↦ densityThreshold W p q n δ) c).trans
  gcongr
  · exact expected_conditional_block_information_le W p q n
  · exact conditional_block_packing_le W p q hn hδ (Fintype.card L)

noncomputable def commonThreshold (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (n : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * (W.comp (FiniteChannel.ofRows q)).mutualInformation p - (n : ℝ) * δ

noncomputable def commonCodingBound (W : FiniteChannel V Y) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (n messages : ℕ) (δ : ℝ) : ℝ :=
  ((n : ℝ) * (W.comp (FiniteChannel.ofRows q)).informationVariance p) / (((n : ℝ) * δ) ^ 2) +
    (messages : ℝ) * Real.exp (-commonThreshold W p q n δ)

theorem expected_block_common_error_le [Nonempty C]
    (W : FiniteChannel V Y) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (c : C) (s : S) :
    (∑ book, superpositionEnsemble (C := C) (S := S) (p.iid n) (conditionalProduct q n) book *
      ∑ y, if ((W.block n).comp (FiniteChannel.ofRows (conditionalProduct q n))).thresholdDecoder
          (p.iid n) (commonThreshold W p q n δ) book.1 y ≠ c
        then (W.block n).transition (book.2 c s) y else 0) ≤
      commonCodingBound W p q n (Fintype.card C) δ := by
  classical
  let T := W.comp (FiniteChannel.ofRows q)
  have hchan : (W.block n).comp (FiniteChannel.ofRows (conditionalProduct q n)) = T.block n := by
    rw [conditionalProduct_channel, ← FiniteChannel.block_comp]
  have h := expected_common_error_le (W.block n) (p.iid n) (conditionalProduct q n)
    (commonThreshold W p q n δ) c s
  apply h.trans
  rw [hchan]
  apply add_le_add
  · rw [T.block_informationDensityLowerTailMass_eq]
    exact T.blockInformationDensity_lowerTail_le p hn hδ
  · rfl

theorem commonCodingBound_nonnegative (W : FiniteChannel V Y)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n messages : ℕ) (δ : ℝ) :
    0 ≤ commonCodingBound W p q n messages δ := by
  unfold commonCodingBound
  have := (W.comp (FiniteChannel.ofRows q)).informationVariance_nonnegative p
  positivity

end CapacityAtlas.ConfidentialBroadcast
