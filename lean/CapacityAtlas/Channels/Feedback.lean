/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.Feedback

namespace CapacityAtlas.Channel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Noiseless strictly causal feedback preserves ordinary finite-DMC capacity. -/
@[capacity_problem "discrete-memoryless-channel-with-feedback", capacity_statement,
  capacity_proposition, capacity_solved, capacity_claim "exact-capacity" 1]
noncomputable def feedbackCapacityStatement [Nonempty X] (channel : FiniteChannel X Y) : Prop :=
  Feedback.operationalCapacityBits channel = channel.informationCapacityBits

end CapacityAtlas.Channel
