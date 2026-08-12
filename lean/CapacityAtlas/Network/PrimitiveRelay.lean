/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalTheory

namespace CapacityAtlas.Network

open CapacityAtlas

/-- A relay observation and destination output followed by an orthogonal noiseless bit-pipe. -/
@[capacity_problem "primitive-relay-channel", capacity_definition]
structure PrimitiveRelayChannel (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z] where
  broadcast : FiniteChannel X (Y × Z)
  relayLinkCapacityBits : ℝ
  relayLinkCapacity_nonnegative : 0 ≤ relayLinkCapacityBits

@[capacity_problem "primitive-relay-channel", capacity_statement]
def primitiveRelayCapacityBoundsStatement {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (theory : ScalarOperationalTheory (PrimitiveRelayChannel X Y Z))
    (compressForwardBound improvedUpperBound cutSetBound :
      PrimitiveRelayChannel X Y Z → ℝ)
    (channel : PrimitiveRelayChannel X Y Z) : Prop :=
  compressForwardBound channel ≤ theory.capacity channel ∧
    theory.capacity channel ≤ improvedUpperBound channel ∧
      improvedUpperBound channel ≤ cutSetBound channel

end CapacityAtlas.Network
