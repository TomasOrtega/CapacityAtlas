/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianMultiuser

namespace CapacityAtlas.Claims

/-- The Gaussian MAC capacity region under separate maximum-codeword power constraints. -/
@[capacity_problem "two-user-gaussian-mac", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem gaussianMAC (P₁ P₂ N : ℝ) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    Gaussian.macCapacityRegion P₁ P₂ N = Gaussian.macRegion P₁ P₂ N := by
  sorry

end CapacityAtlas.Claims
