/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.CompoundChannel.Capacity

namespace CapacityAtlas.Channel

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- Capacity when one encoder and decoder must work for every fixed channel member. -/
@[capacity_problem "compound-discrete-memoryless-channel", capacity_statement,
  capacity_formal_proof, capacity_solved, capacity_claim "exact-capacity" 1]
theorem compoundCapacityStatement [Nonempty X] [Nonempty S]
    (channels : S → FiniteChannel X Y) :
    CompoundChannel.operationalCapacityBits channels =
      CompoundChannel.informationCapacityBits channels :=
  CapacityAtlasCompound.compoundCapacity channels

end CapacityAtlas.Channel
