/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.Network.NoiselessMulticast

namespace CapacityAtlas.Claims

/-- Single-source topological processing on a finite noiseless acyclic network. -/
@[capacity_problem "noiseless-multicast-network", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem multicast {vertices edges : ℕ} (G : NoiselessMulticast.Network vertices edges) :
    G.capacity = G.minCut := by
  sorry

end CapacityAtlas.Claims
