/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.CommonMessageBroadcastInformation

namespace CapacityAtlas.Channel

variable {J X : Type*} {Y : J → Type*}
variable [Fintype J] [DecidableEq J] [Fintype X] [∀ j, Fintype (Y j)]

/-- One common message must be reliably decoded from every receiver's own output. -/
@[capacity_problem "finite-common-message-broadcast-channel", capacity_statement,
  capacity_proposition, capacity_solved, capacity_claim "exact-capacity" 1]
noncomputable def commonMessageBroadcastCapacityStatement [Nonempty J] [Nonempty X]
    (channel : FiniteChannel X ((j : J) → Y j)) : Prop :=
  CommonMessageBroadcast.operationalCapacityBits
      (CommonMessageBroadcast.receiverChannels channel) =
    CommonMessageBroadcast.informationCapacityBits
      (CommonMessageBroadcast.receiverChannels channel)

end CapacityAtlas.Channel
