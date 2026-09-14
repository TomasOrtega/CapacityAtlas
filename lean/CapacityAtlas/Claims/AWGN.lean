/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianOperational

namespace CapacityAtlas.Claims

/-- Operational real AWGN capacity with maximum-codeword average power. -/
@[capacity_problem "additive-white-gaussian-noise-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem awgn (P N : ℝ) (hP : 0 ≤ P) (hN : 0 < N) :
    Gaussian.capacity P N = Gaussian.awgnFormula P N := by
  sorry

end CapacityAtlas.Claims
