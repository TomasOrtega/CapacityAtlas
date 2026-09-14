/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianStateFeedback

namespace CapacityAtlas.Claims

/-- Ozarow's capacity region under separate expected-power constraints and noiseless output feedback. -/
@[capacity_problem "two-user-gaussian-mac-with-feedback", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem gaussianMACFeedback (P₁ P₂ N : ℝ) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    Gaussian.feedbackMACCapacityRegion P₁ P₂ N = Gaussian.ozarowRegion P₁ P₂ N := by
  sorry

end CapacityAtlas.Claims
