/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasCompound/blob/1d5cbdc0a8cfb5d034facdb8d1e2473bb3c40ebe/CapacityAtlasCompound.lean
Adapted module imports; certificate types unfold the canonical proposition.
-/

import CapacityAtlasForMathlib.InformationTheory.CompoundChannel.Achievability
import CapacityAtlasForMathlib.InformationTheory.CompoundChannel.Converse

open CapacityAtlas

namespace CapacityAtlasCompound

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- The finite compound capacity is the maximum of the least member information. -/
theorem compoundCapacity [Nonempty X] [Nonempty S]
    (channels : S → FiniteChannel X Y) :
    CompoundChannel.operationalCapacityBits channels =
      CompoundChannel.informationCapacityBits channels := by
  apply le_antisymm (operationalCapacityBits_le_informationCapacityBits channels)
  have hbounded := achievableRates_bddAbove channels
  apply le_of_forall_lt_imp_le_of_dense
  intro rate hrate
  apply le_csSup hbounded
  apply Or.inr
  by_cases hnonpos : rate ≤ 0
  · exact CompoundChannel.achievableRate_of_nonpos channels hnonpos
  · exact achievableRate_of_lt_informationCapacityBits channels (le_of_not_ge hnonpos) hrate

/-- Compactness gives an input attaining the displayed maximum. -/
theorem exists_capacityAchieving_input [Nonempty X] [Nonempty S]
    (channels : S → FiniteChannel X Y) :
    ∃ input : FiniteDistribution X,
      CompoundChannel.worstInformationBits channels input =
        CompoundChannel.operationalCapacityBits channels := by
  rw [compoundCapacity channels]
  exact CompoundChannel.exists_capacityAchieving_input channels

end CapacityAtlasCompound
