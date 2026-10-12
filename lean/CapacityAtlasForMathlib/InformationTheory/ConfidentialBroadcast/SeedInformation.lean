/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.SeedCoding

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {S L Y : Type*} [Fintype S] [Fintype L] [Fintype Y]

/-- Average the private seed while retaining the public input of the channel. -/
noncomputable def averageSeed (W : FiniteChannel (S × L) Y) (q : S → FiniteDistribution L) :
    FiniteChannel S Y :=
  ofRows fun s ↦ (W.encoded (fun l ↦ (s, l))).outputDistribution (q s)

theorem averageSeed_outputDistribution (W : FiniteChannel (S × L) Y)
    (p : FiniteDistribution S) (q : S → FiniteDistribution L) :
    (W.averageSeed q).outputDistribution p = W.outputDistribution (p.joint q) := by
  ext y
  change (∑ s, p s * ∑ l, q s l * W.transition (s, l) y) =
    ∑ sl : S × L, (p sl.1 * q sl.1 sl.2) * W.transition sl y
  simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- The channel chain rule isolates the information carried by the seed. -/
theorem mutualInformation_averageSeed (W : FiniteChannel (S × L) Y)
    (p : FiniteDistribution S) (q : S → FiniteDistribution L) :
    W.mutualInformation (p.joint q) = (W.averageSeed q).mutualInformation p +
      ∑ s, p s * (W.encoded (fun l ↦ (s, l))).mutualInformation (q s) := by
  have hrow (s : S) (l : L) :
      (W.encoded (fun k ↦ (s, k))).rowDistribution l = W.rowDistribution (s, l) := by
    ext y
    rfl
  rw [mutualInformation, ← averageSeed_outputDistribution]
  simp only [mutualInformation, conditionalOutputEntropy, FiniteDistribution.joint_apply,
    Fintype.sum_prod_type, averageSeed, rowDistribution_ofRows,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, hrow]
  ring

theorem mutualInformationBits_averageSeed (W : FiniteChannel (S × L) Y)
    (p : FiniteDistribution S) (q : S → FiniteDistribution L) :
    W.mutualInformationBits (p.joint q) = (W.averageSeed q).mutualInformationBits p +
      ∑ s, p s * (W.encoded (fun l ↦ (s, l))).mutualInformationBits (q s) := by
  simp only [mutualInformationBits, mutualInformation_averageSeed, add_div,
    Finset.sum_div, mul_div_assoc]

/-- Decoder error expressed directly under the uniform input distribution. -/
noncomputable def uniformDecoderError [Nonempty L] (W : FiniteChannel L Y)
    (decode : Y → L) : ℝ := by
  classical
  exact ∑ l, (FiniteDistribution.uniform L) l *
    ∑ y, if decode y ≠ l then W.transition l y else 0

theorem uniformDecoderError_nonnegative [Nonempty L] (W : FiniteChannel L Y)
    (decode : Y → L) : 0 ≤ W.uniformDecoderError decode := by
  classical
  exact Finset.sum_nonneg fun l _ ↦ mul_nonneg
    ((FiniteDistribution.uniform L).nonnegative l)
    (Finset.sum_nonneg fun y _ ↦ by split_ifs; exact W.nonnegative l y; rfl)

theorem uniformDecoderError_fano [Nonempty L] [DecidableEq L]
    (W : FiniteChannel L Y) (decode : Y → L) :
    Real.log (Fintype.card L) / Real.log 2 ≤
      W.mutualInformationBits (FiniteDistribution.uniform L) + 1 +
        W.uniformDecoderError decode * (Real.log (Fintype.card L) / Real.log 2) := by
  have hf := W.fano_uniform decode
  let code : OneShotCode W L := { encode := id, decode := decode }
  change Real.log (Fintype.card L) ≤
    W.mutualInformation (FiniteDistribution.uniform L) + Real.log 2 +
      code.averageErrorProbability * Real.log (Fintype.card L) at hf
  have he : code.averageErrorProbability =
      W.uniformDecoderError decode := by
    classical
    simp only [OneShotCode.averageErrorProbability_eq,
      OneShotCode.errorProbability_eq_sum_decode_ne, uniformDecoderError,
      FiniteDistribution.uniform_apply, ← Finset.mul_sum]
    congr 1
    apply Fintype.sum_congr
    intro l
    apply Fintype.sum_congr
    intro y
    by_cases h : decode y = l <;> simp [code, h]
  rw [he] at hf
  have hb := div_le_div_of_nonneg_right hf (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  simpa only [add_div, mul_div_assoc, div_self (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
    mutualInformationBits] using hb

/-- Decodable private randomness removes its rate from the information about the message. -/
theorem averageSeed_information_le [Nonempty L] [DecidableEq L]
    (W : FiniteChannel (S × L) Y) (p : FiniteDistribution S) (decode : S → Y → L) :
    (W.averageSeed (fun _ ↦ FiniteDistribution.uniform L)).mutualInformationBits p ≤
      W.mutualInformationBits (p.joint (fun _ ↦ FiniteDistribution.uniform L)) -
        Real.log (Fintype.card L) / Real.log 2 + 1 +
      (∑ s, p s * (W.encoded (fun l ↦ (s, l))).uniformDecoderError (decode s)) *
        (Real.log (Fintype.card L) / Real.log 2) := by
  let h := Real.log (Fintype.card L) / Real.log 2
  have hf : h ≤ (∑ s, p s *
      (W.encoded (fun l ↦ (s, l))).mutualInformationBits (FiniteDistribution.uniform L)) + 1 +
      (∑ s, p s * (W.encoded (fun l ↦ (s, l))).uniformDecoderError (decode s)) * h := by
    calc
      h = ∑ s, p s * h := by
        rw [← Finset.sum_mul, FiniteDistribution.sum_probability_eq_one, one_mul]
      _ ≤ ∑ s, p s *
          ((W.encoded (fun l ↦ (s, l))).mutualInformationBits (FiniteDistribution.uniform L) + 1 +
            (W.encoded (fun l ↦ (s, l))).uniformDecoderError (decode s) * h) := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left
          ((W.encoded (fun l ↦ (s, l))).uniformDecoderError_fano (decode s)) (p.nonnegative s)
      _ = _ := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, ← mul_assoc,
          ← Finset.sum_mul, FiniteDistribution.sum_probability_eq_one]
  have hi := W.mutualInformationBits_averageSeed p (fun _ ↦ FiniteDistribution.uniform L)
  dsimp [h] at hf
  linarith

theorem uniformDecoderError_encoded {V : Type*} [Fintype V] [Nonempty L] [DecidableEq L]
    (W : FiniteChannel V Y) (book : L → V) (decode : Y → L) :
    (W.encoded book).uniformDecoderError decode =
      ({ encode := book, decode := decode } : OneShotCode W L).averageErrorProbability := by
  classical
  simp only [uniformDecoderError, FiniteDistribution.uniform_apply, ← Finset.mul_sum,
    OneShotCode.averageErrorProbability_eq, OneShotCode.errorProbability_eq_sum_decode_ne]
  congr 1
  apply Fintype.sum_congr
  intro l
  apply Fintype.sum_congr
  intro y
  by_cases h : decode y = l <;> simp [encoded, h]

end CapacityAtlas.FiniteChannel
