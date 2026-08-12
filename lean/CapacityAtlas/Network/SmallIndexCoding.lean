/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.IndexCoding

namespace CapacityAtlas.IndexCoding

/-- The published composite-coding formula covers every rate vector through five messages. -/
@[capacity_problem "index-coding-at-most-five-messages", capacity_statement]
def indexCodingAtMostFiveMessagesCapacityRegions
    (operationalRegion compositeCodingRegion :
      ∀ messageCount : ℕ,
        Instance (Fin messageCount) (Fin messageCount) →
          Set (Fin messageCount → ℝ)) : Prop :=
  ∀ messageCount : ℕ, 0 < messageCount → messageCount ≤ 5 →
    ∀ problem : Instance (Fin messageCount) (Fin messageCount),
      operationalRegion messageCount problem = compositeCodingRegion messageCount problem

/-- Shannon-polymatroid bounds are tight for every multiple-unicast instance up to five messages. -/
@[capacity_problem "index-coding-at-most-five-messages", capacity_statement]
def indexCodingAtMostFiveMessagesStatement : Prop :=
  ∀ messageCount : ℕ, 0 < messageCount → messageCount ≤ 5 →
    ∀ problem : Instance (Fin messageCount) (Fin messageCount),
      symmetricCapacity problem = shannonPolymatroidOuterBound problem

end CapacityAtlas.IndexCoding
