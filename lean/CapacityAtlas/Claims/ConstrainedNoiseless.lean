/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.FiniteStateOperational

namespace CapacityAtlas.Claims

/-- The noiseless binary (1,infinity) constrained channel has log(phi) capacity. -/
@[capacity_problem "no-consecutive-ones-noiseless-channel", capacity_claim "operational-capacity" 2,
  capacity_statement, capacity_solved]
theorem constrainedNoiseless :
    FiniteStateOperational.capacity
        (FiniteStateOperational.memoryless (FiniteChannel.identity Bool))
        (FiniteStateOperational.fixedInitial ()) FiniteStateOperational.noConsecutiveOnes =
      Real.logb 2 ((1 + Real.sqrt 5) / 2) := by
  sorry

end CapacityAtlas.Claims
