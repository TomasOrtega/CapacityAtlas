/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.PrivateMessageBroadcast

namespace CapacityAtlas.Claims

/-- The fixed two-auxiliary Marton inner bound and UV outer bound, with closures. -/
@[capacity_problem "general-two-receiver-broadcast-channel", capacity_claim "marton-uv-bounds" 1,
  capacity_statement, capacity_solved]
theorem broadcastBounds {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteBroadcastChannel X Y₁ Y₂) :
    PrivateMessageBroadcast.martonRegion W ⊆ PrivateMessageBroadcast.capacityRegion W ∧
      PrivateMessageBroadcast.capacityRegion W ⊆ PrivateMessageBroadcast.uvRegion W := by
  sorry

/-- Independently tracked marton achievability. -/
@[capacity_problem "general-two-receiver-broadcast-channel", capacity_claim "marton-achievability" 1,
  capacity_statement, capacity_solved]
theorem broadcastMarton {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteBroadcastChannel X Y₁ Y₂) :
    PrivateMessageBroadcast.martonRegion W ⊆ PrivateMessageBroadcast.capacityRegion W := by
  sorry

/-- Independently tracked uv converse. -/
@[capacity_problem "general-two-receiver-broadcast-channel", capacity_claim "uv-converse" 1,
  capacity_statement, capacity_solved]
theorem broadcastUV {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    [Nonempty X] [Nonempty Y₁] [Nonempty Y₂]
    (W : FiniteBroadcastChannel X Y₁ Y₂) :
    PrivateMessageBroadcast.capacityRegion W ⊆ PrivateMessageBroadcast.uvRegion W := by
  sorry

end CapacityAtlas.Claims
