/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.FiniteStateOperational
import CapacityAtlas.Channels.Trapdoor

namespace CapacityAtlas.Claims

/-- Feedback trapdoor capacity with a fixed state known to both terminals. -/
@[capacity_problem "trapdoor-channel-with-feedback", capacity_claim "operational-capacity" 2,
  capacity_statement, capacity_solved]
theorem trapdoorFeedback (initial : Bool) :
    FiniteStateOperational.feedbackCapacity Channel.trapdoorFeedbackModel
        (FiniteStateOperational.fixedInitial initial) (fun _ _ ↦ True) =
      Real.logb 2 ((1 + Real.sqrt 5) / 2) := by
  sorry

end CapacityAtlas.Claims
