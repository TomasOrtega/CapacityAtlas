/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.RandomCoding

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast

variable {U V Y C S : Type*} [Fintype U] [Fintype V] [Fintype Y]
  [Fintype C] [Fintype S] [DecidableEq C] [DecidableEq S]

/-- Clouds are independent; the satellites within each cloud share its conditional law. -/
def superpositionEnsemble (p : FiniteDistribution U) (q : U → FiniteDistribution V) :
    FiniteDistribution ((C → U) × (C → S → V)) :=
  (FiniteDistribution.productFamily (fun _ : C ↦ p)).joint fun cloud ↦
    FiniteDistribution.productFamily fun c : C ↦
      FiniteDistribution.productFamily fun _ : S ↦ q (cloud c)

def satelliteEnsemble (q : U → FiniteDistribution V) (cloud : C → U) :
    FiniteDistribution (C → S → V) :=
  FiniteDistribution.productFamily fun c : C ↦
    FiniteDistribution.productFamily fun _ : S ↦ q (cloud c)

omit [Fintype U] in
/-- A fixed satellite has the conditional law associated with its cloud. -/
theorem expected_satellite_observable (q : U → FiniteDistribution V)
    (cloud : C → U) (c : C) (s : S) (f : V → ℝ) :
    (∑ books, satelliteEnsemble q cloud books * f (books c s)) =
      ∑ v, q (cloud c) v * f v := by
  rw [satelliteEnsemble, FiniteDistribution.sum_productFamily_mul_eval
    (fun j : C ↦ FiniteDistribution.productFamily (fun _ : S ↦ q (cloud j)))
    (fun row : S → V ↦ f (row s)) c]
  exact FiniteDistribution.sum_productFamily_mul_eval (fun _ : S ↦ q (cloud c)) f s

/-- Averaging a satellite's output recovers the cloud-to-output channel. -/
theorem expected_common_error_eq [Nonempty C]
    (W : FiniteChannel V Y) (q : U → FiniteDistribution V) (p : FiniteDistribution U)
    (cloud : C → U) (threshold : ℝ) (c : C) (s : S) :
    (∑ books, satelliteEnsemble q cloud books *
      ∑ y, if (W.comp (FiniteChannel.ofRows q)).thresholdDecoder p threshold cloud y ≠ c
        then W.transition (books c s) y else 0) =
      ((W.comp (FiniteChannel.ofRows q)).thresholdCode p threshold cloud).errorProbability c := by
  classical
  rw [OneShotCode.errorProbability_eq_sum_decode_ne]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro y
  change (∑ books, satelliteEnsemble q cloud books *
    if (W.comp (FiniteChannel.ofRows q)).thresholdDecoder p threshold cloud y ≠ c
      then W.transition (books c s) y else 0) = _
  rw [expected_satellite_observable q cloud c s
    (fun v ↦ if (W.comp (FiniteChannel.ofRows q)).thresholdDecoder p threshold cloud y ≠ c
      then W.transition v y else 0)]
  simp only [FiniteChannel.thresholdCode]
  split_ifs <;> simp_all [FiniteChannel.comp, FiniteChannel.ofRows]

/-- Common-message decoding has the ordinary packing bound under superposition sampling. -/
theorem expected_common_error_le [Nonempty C]
    (W : FiniteChannel V Y) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (threshold : ℝ) (c : C) (s : S) :
    (∑ book, superpositionEnsemble (C := C) (S := S) p q book *
      ∑ y, if (W.comp (FiniteChannel.ofRows q)).thresholdDecoder p threshold book.1 y ≠ c
        then W.transition (book.2 c s) y else 0) ≤
      (W.comp (FiniteChannel.ofRows q)).informationDensityLowerTailMass p threshold +
        (Fintype.card C : ℝ) * Real.exp (-threshold) := by
  classical
  simp only [superpositionEnsemble, FiniteDistribution.joint_apply,
    Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
  change (∑ cloud, FiniteDistribution.productFamily (fun _ : C ↦ p) cloud *
    ∑ books, satelliteEnsemble q cloud books *
      ∑ y, if (W.comp (FiniteChannel.ofRows q)).thresholdDecoder p threshold cloud y ≠ c
        then W.transition (books c s) y else 0) ≤ _
  simp_rw [expected_common_error_eq]
  exact (W.comp (FiniteChannel.ofRows q)).expected_thresholdCode_errorProbability_le
    p threshold c

/-- Conditional satellite decoding obeys the packing bound for the realized cloud law. -/
theorem expected_satellite_error_le [Nonempty S]
    (W : FiniteChannel V Y) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (threshold : U → ℝ) (c : C) (s : S) :
    (∑ book, superpositionEnsemble (C := C) (S := S) p q book *
      (W.thresholdCode (q (book.1 c)) (threshold (book.1 c)) (book.2 c)).errorProbability s) ≤
      ∑ u, p u * (W.informationDensityLowerTailMass (q u) (threshold u) +
        (Fintype.card S : ℝ) * Real.exp (-threshold u)) := by
  classical
  simp only [superpositionEnsemble, FiniteDistribution.joint_apply,
    Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
  calc
    _ = ∑ cloud, FiniteDistribution.productFamily (fun _ : C ↦ p) cloud *
        ∑ row : S → V, FiniteDistribution.productFamily (fun _ : S ↦ q (cloud c)) row *
          (W.thresholdCode (q (cloud c)) (threshold (cloud c)) row).errorProbability s := by
      apply Fintype.sum_congr
      intro cloud
      congr 1
      exact FiniteDistribution.sum_productFamily_mul_eval
        (fun j : C ↦ FiniteDistribution.productFamily (fun _ : S ↦ q (cloud j)))
        (fun row : S → V ↦
          (W.thresholdCode (q (cloud c)) (threshold (cloud c)) row).errorProbability s) c
    _ ≤ ∑ cloud, FiniteDistribution.productFamily (fun _ : C ↦ p) cloud *
        (W.informationDensityLowerTailMass (q (cloud c)) (threshold (cloud c)) +
          (Fintype.card S : ℝ) * Real.exp (-threshold (cloud c))) := by
      apply Finset.sum_le_sum
      intro cloud _
      apply mul_le_mul_of_nonneg_left _ (FiniteDistribution.probability_nonnegative _ _)
      exact W.expected_thresholdCode_errorProbability_le (q (cloud c)) (threshold (cloud c)) s
    _ = _ := FiniteDistribution.sum_productFamily_mul_eval (fun _ : C ↦ p)
      (fun u ↦ W.informationDensityLowerTailMass (q u) (threshold u) +
        (Fintype.card S : ℝ) * Real.exp (-threshold u)) c

end CapacityAtlas.ConfidentialBroadcast
