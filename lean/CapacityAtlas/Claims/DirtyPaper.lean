/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianStateFeedback

namespace CapacityAtlas.Claims

/-- Noncausal independent Gaussian interference at the encoder causes no capacity loss. -/
@[capacity_problem "costa-dirty-paper-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem dirtyPaper (P Q N : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hN : 0 < N) :
    Gaussian.dirtyPaperCapacity P Q N = Gaussian.awgnFormula P N := by
  sorry

end CapacityAtlas.Claims
