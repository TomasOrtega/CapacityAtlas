/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess.Capacity

namespace CapacityAtlas.Channel

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- The average-error capacity region of a finite two-user MAC. -/
@[capacity_problem "two-user-discrete-memoryless-mac", capacity_statement,
  capacity_formal_proof, capacity_solved, capacity_claim "exact-capacity" 1]
theorem multipleAccessCapacityStatement [Nonempty X₁] [Nonempty X₂]
    (channel : FiniteChannel (X₁ × X₂) Y) :
  MultipleAccess.operationalRegion channel = MultipleAccess.informationRegion channel :=
  CapacityAtlasMAC.capacityRegion channel

end CapacityAtlas.Channel
