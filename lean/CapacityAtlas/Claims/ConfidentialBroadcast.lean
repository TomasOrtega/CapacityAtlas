/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Capacity

namespace CapacityAtlas.Claims

@[capacity_problem "broadcast-channel-confidential-messages", capacity_statement,
  capacity_formal_proof, capacity_solved, capacity_claim "capacity-region" 1]
theorem confidentialBroadcastCapacity {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (W : FiniteBroadcastChannel X Y Z) :
    ConfidentialBroadcast.capacityRegion W = ConfidentialBroadcast.informationRegion W :=
  ConfidentialBroadcast.capacityRegion_eq_informationRegion W

end CapacityAtlas.Claims
