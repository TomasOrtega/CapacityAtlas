/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianStateFeedback

namespace CapacityAtlas.Claims

/-- Iid ergodic real fading known only to the receiver, with finite expected information. -/
@[capacity_problem "gaussian-fading-receiver-state", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem fading (law : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure law]
    (P N : ℝ) (hP : 0 ≤ P) (hN : 0 < N)
    (hfinite : MeasureTheory.Integrable (fun h ↦ Gaussian.awgnFormula (h ^ 2 * P) N) law) :
    Gaussian.fadingCapacity law P N = Gaussian.fadingFormula law P N := by
  sorry

end CapacityAtlas.Claims
