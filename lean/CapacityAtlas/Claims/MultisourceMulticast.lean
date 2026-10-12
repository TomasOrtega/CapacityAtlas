/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.Capacity

namespace CapacityAtlas.Claims

@[capacity_problem "noiseless-multisource-multicast-network", capacity_statement,
  capacity_formal_proof, capacity_solved, capacity_claim "capacity-region" 1]
theorem multisourceMulticastCapacity {vertices edges sources : ℕ}
    (G : Multisource.Network vertices edges sources) :
    G.capacityRegion = G.cutRegion := G.capacityRegion_eq_cutRegion

end CapacityAtlas.Claims
