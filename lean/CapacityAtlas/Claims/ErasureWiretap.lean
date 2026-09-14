/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.WiretapOperational
import CapacityAtlas.Channels.Binary

namespace CapacityAtlas.Claims

/-- Strong-secrecy capacity when the legitimate channel is noiseless and Eve sees erasures. -/
@[capacity_problem "erasure-wiretap-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem erasureWiretap (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    WiretapOperational.capacity
      ({ legitimate := FiniteChannel.identity Bool
         eavesdropper := Channel.binaryErasure ε hε0 hε1 } :
          FiniteWiretapChannel Bool Bool (Option Bool)) = ε := by
  sorry

end CapacityAtlas.Claims
