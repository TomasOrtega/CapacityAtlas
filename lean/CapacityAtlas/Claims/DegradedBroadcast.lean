/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.PrivateMessageBroadcast

namespace CapacityAtlas.Claims

/-- The private-message operational region of a degraded finite broadcast channel. -/
@[capacity_problem "physically-degraded-broadcast-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem degradedBroadcast {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteBroadcastChannel X Y₁ Y₂) (hW : PrivateMessageBroadcast.IsDegraded W) :
    PrivateMessageBroadcast.capacityRegion W = superpositionRegion W := by
  sorry

end CapacityAtlas.Claims
