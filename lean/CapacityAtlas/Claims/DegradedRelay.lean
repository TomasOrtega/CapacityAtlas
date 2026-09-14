/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.Network.RelayOperational

namespace CapacityAtlas.Claims

/-- The physically degraded relay capacity under strictly causal relaying. -/
@[capacity_problem "physically-degraded-relay-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem degradedRelay {X R Z Y : Type*} [Fintype X] [Fintype R] [Fintype Z] [Fintype Y]
    [Nonempty X] [Nonempty R] [Nonempty Z] [Nonempty Y]
    (W : Relay.Channel X R Z Y) (hW : Relay.IsDegraded W) :
    Relay.capacity W = Relay.decodeForward W := by
  sorry

end CapacityAtlas.Claims
