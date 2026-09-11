/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.CausalState

namespace CapacityAtlas.Channel

attribute [local instance] Classical.propDecidable

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- Shannon's capacity formula for iid state observed causally only by the encoder. -/
@[capacity_problem "causal-state-information-channel", capacity_statement,
  capacity_proposition, capacity_solved, capacity_claim "exact-capacity" 1]
noncomputable def causalStateCapacityStatement [Nonempty X] (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) : Prop :=
  CausalState.operationalCapacityBits state channels =
    (CausalState.strategyChannel state channels).informationCapacityBits

end CapacityAtlas.Channel
