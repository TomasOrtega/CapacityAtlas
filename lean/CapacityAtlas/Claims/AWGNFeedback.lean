/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianStateFeedback

namespace CapacityAtlas.Claims

/-- Real AWGN feedback capacity under expected block-average power. -/
@[capacity_problem "awgn-channel-with-feedback", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem awgnFeedback (P N : ℝ) (hP : 0 ≤ P) (hN : 0 < N) :
    Gaussian.feedbackCapacity P N = Gaussian.awgnFormula P N := by
  sorry

end CapacityAtlas.Claims
