/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.FiniteStateOperational
import CapacityAtlas.Channels.Binary

namespace CapacityAtlas.Claims

/-- Exact feedback capacity of the binary (1,infinity) input-constrained erasure channel. -/
@[capacity_problem "constrained-bec-with-feedback", capacity_claim "operational-capacity" 2,
  capacity_statement, capacity_solved]
theorem constrainedBEC (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    FiniteStateOperational.feedbackCapacity
        (FiniteStateOperational.memoryless (Channel.binaryErasure ε hε0 hε1))
        (FiniteStateOperational.fixedInitial ()) FiniteStateOperational.noConsecutiveOnes =
      sSup {r : ℝ | ∃ p : ℝ, 0 ≤ p ∧ p ≤ (1 / 2 : ℝ) ∧
        r = (1 - ε) * (Real.binEntropy p / Real.log 2) / (1 + (1 - ε) * p)} := by
  sorry

end CapacityAtlas.Claims
