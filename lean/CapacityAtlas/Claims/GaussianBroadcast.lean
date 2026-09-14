/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianMultiuser

namespace CapacityAtlas.Claims

/-- The scalar Gaussian broadcast power-splitting capacity region, stronger receiver first. -/
@[capacity_problem "degraded-gaussian-broadcast-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem gaussianBroadcast (P N₁ N₂ : ℝ) (hP : 0 ≤ P) (hN₁ : 0 < N₁) (hN : N₁ ≤ N₂) :
    Gaussian.broadcastCapacityRegion P N₁ N₂ = Gaussian.broadcastRegion P N₁ N₂ := by
  sorry

end CapacityAtlas.Claims
