/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.NoncausalState

namespace CapacityAtlas.Claims

/-- The Gel'fand--Pinsker formula for iid state seen noncausally only by the encoder. -/
@[capacity_problem "gelfand-pinsker-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem gelfandPinsker {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
    [Nonempty S] [Nonempty X] [Nonempty Y]
    (p : FiniteDistribution S) (W : S → FiniteChannel X Y) :
    NoncausalState.capacity p W = NoncausalState.informationCapacity p W := by
  sorry

end CapacityAtlas.Claims
