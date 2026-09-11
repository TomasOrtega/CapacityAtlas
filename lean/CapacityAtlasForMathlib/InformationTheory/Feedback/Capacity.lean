/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasFeedback/blob/b35299f221ad1c17ccbafb45082c22a5379a99e9/CapacityAtlasFeedback.lean
Adapted module imports; certificate types unfold the canonical proposition.
-/

import CapacityAtlasForMathlib.InformationTheory.Feedback.Converse
import CapacityAtlasForMathlib.InformationTheory.FiniteChannelOptimization

open CapacityAtlas

namespace CapacityAtlasFeedback

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Strictly causal noiseless feedback preserves the finite-DMC information capacity. -/
theorem feedbackCapacity [Nonempty X] (channel : FiniteChannel X Y) :
    Feedback.operationalCapacityBits channel = channel.informationCapacityBits := by
  apply le_antisymm (operationalCapacityBits_le_informationCapacityBits channel)
  apply le_of_forall_lt_imp_le_of_dense
  intro rate hrate
  apply le_csSup (achievableRates_bddAbove channel)
  exact Feedback.achievableRate_of_ordinary
    (channel.achievableRate_of_lt_informationCapacityBits hrate)

/-- Feedback and ordinary fixed-blocklength operational capacities agree. -/
theorem feedbackCapacity_eq_ordinary [Nonempty X] (channel : FiniteChannel X Y) :
    Feedback.operationalCapacityBits channel = channel.operationalCapacityBits := by
  rw [feedbackCapacity channel]
  exact channel.codingTheorem.symm

/-- An ordinary input distribution attains the feedback capacity's information formula. -/
theorem exists_capacityAchieving_input [Nonempty X] (channel : FiniteChannel X Y) :
    ∃ input : FiniteDistribution X,
      channel.mutualInformationBits input = Feedback.operationalCapacityBits channel := by
  rw [feedbackCapacity channel]
  exact channel.exists_capacityAchieving_input

end CapacityAtlasFeedback
