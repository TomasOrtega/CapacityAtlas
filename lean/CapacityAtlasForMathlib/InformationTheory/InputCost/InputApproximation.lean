/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0

Adapted from TomasOrtega/CapacityAtlasInputCost, commit 5e6a432bc276aa4e08b7f27658daf40e029cda48,
CapacityAtlasCost/InputApproximation.lean. Imports and certificate types use the monorepo modules.
-/

import CapacityAtlasForMathlib.InformationTheory.InputCost
import CapacityAtlasForMathlib.InformationTheory.FiniteMixture

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {X : Type*} [Fintype X]

theorem expectedCost_atom [DecidableEq X] (point : X) (cost : X → ℝ) :
    (atom point).expectedCost cost = cost point :=
  sum_atom_mul point cost

theorem expectedCost_binaryMixture (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (left right : FiniteDistribution X) (cost : X → ℝ) :
    (binaryMixture t ht0 ht1 left right).expectedCost cost =
      (1 - t) * left.expectedCost cost + t * right.expectedCost cost :=
  sum_binaryMixture_mul t ht0 ht1 left right cost

end FiniteDistribution

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem exists_strictCost_input_of_lt_mutualInformationBits
    (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (cost : X → ℝ) (budget : ℝ) (hinput : input.IsAdmissibleCost cost budget)
    (hcheap : ∃ point, cost point < budget) {rate : ℝ}
    (hrate : rate < channel.mutualInformationBits input) :
    ∃ improved : FiniteDistribution X,
      improved.expectedCost cost < budget ∧ rate < channel.mutualInformationBits improved := by
  classical
  obtain ⟨point, hpoint⟩ := hcheap
  let information := channel.mutualInformationBits input
  have hnonneg : 0 ≤ information :=
    div_nonneg (channel.mutualInformation_nonnegative input) (Real.log_nonneg (by norm_num))
  have hdenom : 0 < information + 1 := by linarith
  have hgap : 0 < (information - rate) / (information + 1) :=
    div_pos (sub_pos.mpr hrate) hdenom
  obtain ⟨t, ht0, htbound⟩ := exists_between (lt_min (by norm_num : (0 : ℝ) < 1) hgap)
  have ht1 : t ≤ 1 := (lt_of_lt_of_le htbound (min_le_left _ _)).le
  have hscaled : t * (information + 1) < information - rate :=
    (lt_div_iff₀ hdenom).mp (lt_of_lt_of_le htbound (min_le_right _ _))
  refine ⟨FiniteDistribution.binaryMixture t ht0.le ht1 input (FiniteDistribution.atom point),
    ?_, ?_⟩
  · rw [FiniteDistribution.expectedCost_binaryMixture, FiniteDistribution.expectedCost_atom]
    have hinputScaled := mul_le_mul_of_nonneg_left hinput (sub_nonneg.mpr ht1)
    have hpointScaled := mul_lt_mul_of_pos_left hpoint ht0
    change (1 - t) * input.expectedCost cost ≤ (1 - t) * budget at hinputScaled
    nlinarith
  · apply lt_of_lt_of_le _
      (channel.mutualInformationBits_binaryMixture_atom_ge t ht0.le ht1 input point)
    change rate < (1 - t) * information
    nlinarith

end FiniteChannel

end CapacityAtlas
