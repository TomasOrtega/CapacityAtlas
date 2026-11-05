/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

open scoped BigOperators

namespace CapacityAtlas

/-- A finite-support variable-length one-step channel. -/
structure VariableLengthChannelStep (X Y : Type*) [Fintype X] [Fintype Y]
    [DecidableEq Y] where
  /-- Finite set of output lists that may occur for each input. -/
  support : X → Finset (List Y)
  /-- Conditional mass assigned to each finite output list. -/
  transition : X → List Y → ℝ
  /-- All output-list masses are nonnegative. -/
  nonnegative : ∀ input output, 0 ≤ transition input output
  /-- The masses on the finite output support sum to one for each input. -/
  row_sum : ∀ input, ∑ output ∈ support input, transition input output = 1
  /-- Output lists outside the declared support have zero mass. -/
  zero_outside : ∀ input output, output ∉ support input → transition input output = 0

end CapacityAtlas
