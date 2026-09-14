/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.PrivateMessageBroadcast
import CapacityAtlas.Channels.Broadcast

namespace CapacityAtlas.Claims

/-- The operational private-message region of the registered Blackwell channel. -/
@[capacity_problem "blackwell-broadcast-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem blackwell :
    PrivateMessageBroadcast.capacityRegion Channel.blackwellBroadcastChannel =
      Channel.blackwellCapacityRegion := by
  sorry

end CapacityAtlas.Claims
