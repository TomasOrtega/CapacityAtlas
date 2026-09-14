/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannel

namespace CapacityAtlas.FiniteChannel

variable {M X Y : Type*} [Fintype M] [Fintype X] [Fintype Y]

/-- A channel with its input symbols selected by a deterministic encoder. -/
@[capacity_shared_api]
def encoded (channel : FiniteChannel X Y) (encode : M → X) : FiniteChannel M Y where
  transition message output := channel.transition (encode message) output
  nonnegative message output := channel.nonnegative (encode message) output
  row_sum message := channel.row_sum (encode message)

@[simp, capacity_shared_api]
theorem encoded_transition (channel : FiniteChannel X Y) (encode : M → X)
    (message : M) (output : Y) :
    (channel.encoded encode).transition message output =
      channel.transition (encode message) output :=
  rfl

end CapacityAtlas.FiniteChannel
