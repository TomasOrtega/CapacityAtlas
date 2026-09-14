/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlas.Network.CycleIndexCoding

namespace CapacityAtlas.Claims

/-- The directed cycle with k+3 messages has symmetric capacity 1/(k+2), for unrestricted zero-error codes. -/
@[capacity_problem "directed-cycle-index-coding", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem directedIndexCycle (k : ℕ) :
    IndexCoding.symmetricCapacity (IndexCoding.directedCycle k) = 1 / ((k : ℝ) + 2) := by
  sorry

end CapacityAtlas.Claims
