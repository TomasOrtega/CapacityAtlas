/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlas.Network.CycleIndexCoding

namespace CapacityAtlas.Claims

/-- The undirected five-cycle has unrestricted zero-error symmetric capacity 2/5. -/
@[capacity_problem "five-cycle-index-coding", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem fiveIndexCycle :
    IndexCoding.symmetricCapacity IndexCoding.undirectedFiveCycle = (2 / 5 : ℝ) := by
  sorry

end CapacityAtlas.Claims
