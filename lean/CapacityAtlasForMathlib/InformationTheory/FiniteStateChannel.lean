/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

open scoped BigOperators

namespace CapacityAtlas

/-- A finite-state one-step channel, including its next-state transition. -/
@[capacity_shared_api]
structure FiniteStateChannel (X State Y : Type*)
    [Fintype X] [Fintype State] [Fintype Y] where
  /-- Joint probability of the output and next state given the input and current state. -/
  transition : X → State → Y → State → ℝ
  /-- All joint output and next-state probabilities are nonnegative. -/
  nonnegative : ∀ input state output nextState,
    0 ≤ transition input state output nextState
  /-- For each input and current state, the output and next-state probabilities sum to one. -/
  row_sum : ∀ input state, ∑ output, ∑ nextState,
    transition input state output nextState = 1

end CapacityAtlas
