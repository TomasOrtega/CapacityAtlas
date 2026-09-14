/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.PrivateMessageBroadcast
import CapacityAtlas.Channels.Broadcast

namespace CapacityAtlas.Claims

/-- Marton/UV bounds specialized to the concrete binary skew-symmetric channel. -/
@[capacity_problem "binary-skew-symmetric-broadcast-channel", capacity_claim "marton-uv-bounds" 1,
  capacity_statement, capacity_solved]
theorem skewBroadcastBounds :
    PrivateMessageBroadcast.martonRegion Channel.binarySkewSymmetricBroadcastChannel ⊆
        PrivateMessageBroadcast.capacityRegion Channel.binarySkewSymmetricBroadcastChannel ∧
      PrivateMessageBroadcast.capacityRegion Channel.binarySkewSymmetricBroadcastChannel ⊆
        PrivateMessageBroadcast.uvRegion Channel.binarySkewSymmetricBroadcastChannel := by
  sorry

/-- Independently tracked marton achievability. -/
@[capacity_problem "binary-skew-symmetric-broadcast-channel", capacity_claim "marton-achievability" 1,
  capacity_statement, capacity_solved]
theorem skewBroadcastMarton :
    PrivateMessageBroadcast.martonRegion Channel.binarySkewSymmetricBroadcastChannel ⊆
        PrivateMessageBroadcast.capacityRegion Channel.binarySkewSymmetricBroadcastChannel := by
  sorry

/-- Independently tracked uv converse. -/
@[capacity_problem "binary-skew-symmetric-broadcast-channel", capacity_claim "uv-converse" 1,
  capacity_statement, capacity_solved]
theorem skewBroadcastUV :
    PrivateMessageBroadcast.capacityRegion Channel.binarySkewSymmetricBroadcastChannel ⊆
        PrivateMessageBroadcast.uvRegion Channel.binarySkewSymmetricBroadcastChannel := by
  sorry

end CapacityAtlas.Claims
