/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.FiniteStateOperational
import CapacityAtlas.Channels.Trapdoor

namespace CapacityAtlas.Claims

/-- Analytic no-feedback bounds. Rounded or extrapolated numerical endpoints are not asserted. -/
@[capacity_problem "trapdoor-channel-without-feedback", capacity_claim "analytic-capacity-bounds" 2,
  capacity_statement, capacity_solved]
theorem trapdoorBounds (initial : Bool) :
    (1 / 2 : ℝ) ≤ FiniteStateOperational.capacity Channel.trapdoorFeedforwardModel
        (FiniteStateOperational.fixedInitial initial) (fun _ _ ↦ True) ∧
      FiniteStateOperational.capacity Channel.trapdoorFeedforwardModel
        (FiniteStateOperational.fixedInitial initial) (fun _ _ ↦ True) ≤ Real.logb 2 (3 / 2 : ℝ) := by
  sorry

/-- Independently tracked repetition achievability. -/
@[capacity_problem "trapdoor-channel-without-feedback", capacity_claim "repetition-achievability" 1,
  capacity_statement, capacity_solved]
theorem trapdoorRepetition (initial : Bool) :
    (1 / 2 : ℝ) ≤ FiniteStateOperational.capacity Channel.trapdoorFeedforwardModel
        (FiniteStateOperational.fixedInitial initial) (fun _ _ ↦ True) := by
  sorry

/-- Independently tracked analytic converse. -/
@[capacity_problem "trapdoor-channel-without-feedback", capacity_claim "analytic-converse" 1,
  capacity_statement, capacity_solved]
theorem trapdoorAnalyticConverse (initial : Bool) :
    FiniteStateOperational.capacity Channel.trapdoorFeedforwardModel
        (FiniteStateOperational.fixedInitial initial) (fun _ _ ↦ True) ≤ Real.logb 2 (3 / 2 : ℝ) := by
  sorry

end CapacityAtlas.Claims
