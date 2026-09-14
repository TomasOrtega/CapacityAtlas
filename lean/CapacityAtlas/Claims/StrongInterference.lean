/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.Network.InterferenceOperational

namespace CapacityAtlas.Claims

/-- The strong-interference region uses the same time-sharing law at both receivers. -/
@[capacity_problem "strong-interference-two-user-dmc", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem strongInterference {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X₁] [Nonempty X₂] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) (hW : W.IsStrongInterference) :
    Interference.capacityRegion W = Interference.strongRegion W := by
  sorry

end CapacityAtlas.Claims
