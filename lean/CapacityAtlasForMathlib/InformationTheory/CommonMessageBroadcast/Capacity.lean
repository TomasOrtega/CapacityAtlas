/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Adapted from TomasOrtega/CapacityAtlasCommonMessage, commit 83923a9a73280ff2d24c71411398438edcc20e4b,
original file CapacityAtlasCommonMessage.lean.
Adapted imports to local proofs; the canonical claim applies the capacity theorem directly.
-/

import CapacityAtlasForMathlib.InformationTheory.CompoundChannel.Capacity
import CapacityAtlasForMathlib.InformationTheory.CommonMessageBroadcast.Reduction

namespace CapacityAtlasCommonMessage

open CapacityAtlas

variable {J X : Type*} {Y : J → Type*}
variable [Fintype J] [Fintype X] [∀ j, Fintype (Y j)]

/-- A common message has the max–min capacity across the receiver marginals. -/
theorem commonMessageCapacity [Nonempty J] [Nonempty X]
    (channels : (j : J) → FiniteChannel X (Y j)) :
    CommonMessageBroadcast.operationalCapacityBits channels =
      CommonMessageBroadcast.informationCapacityBits channels := by
  rw [CommonMessageBroadcast.operationalCapacityBits_eq_taggedChannels,
    CapacityAtlasCompound.compoundCapacity,
    CommonMessageBroadcast.informationCapacityBits_taggedChannels]

/-- One shared input law attains the displayed operational capacity. -/
theorem exists_capacityAchieving_input [Nonempty J] [Nonempty X]
    (channels : (j : J) → FiniteChannel X (Y j)) :
    ∃ input : FiniteDistribution X,
      CommonMessageBroadcast.worstInformationBits channels input =
        CommonMessageBroadcast.operationalCapacityBits channels := by
  rw [commonMessageCapacity channels]
  exact CommonMessageBroadcast.exists_capacityAchieving_input channels

end CapacityAtlasCommonMessage
