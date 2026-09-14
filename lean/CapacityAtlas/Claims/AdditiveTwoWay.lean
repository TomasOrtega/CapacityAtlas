/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.Network.InteractiveTwoWay

namespace CapacityAtlas.Claims

/-- Independent memoryless additive noises give a rectangular capacity region even with adaptation. -/
@[capacity_problem "modulo-additive-two-way-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem additiveTwoWay {G : Type*} [Fintype G] [AddCommGroup G]
    (noise₁ noise₂ : FiniteDistribution G) :
    TwoWay.capacityRegion (TwoWay.additiveChannel noise₁ noise₂) =
      {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
        r.1 ≤ Real.logb 2 (Fintype.card G) - noise₂.entropyBits ∧
        r.2 ≤ Real.logb 2 (Fintype.card G) - noise₁.entropyBits} := by
  sorry

end CapacityAtlas.Claims
