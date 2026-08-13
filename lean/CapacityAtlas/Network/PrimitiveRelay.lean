/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

namespace CapacityAtlas.Network

open CapacityAtlas

/-- A relay observation and destination output followed by an orthogonal noiseless bit-pipe. -/
@[capacity_problem "primitive-relay-channel", capacity_definition]
structure PrimitiveRelayChannel (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z] where
  broadcast : FiniteChannel X (Y × Z)
  relayLinkCapacityBits : ℝ
  relayLinkCapacity_nonnegative : 0 ≤ relayLinkCapacityBits

end CapacityAtlas.Network
