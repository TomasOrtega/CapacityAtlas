/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.AchievabilityClosure
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.ConverseCapacity

namespace CapacityAtlas.ConfidentialBroadcast

/-- The finite broadcast region for a common message and a weakly secret message. -/
@[capacity_shared_api]
theorem capacityRegion_eq_informationRegion {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (W : FiniteBroadcastChannel X Y Z) :
    capacityRegion W = informationRegion W :=
  Set.Subset.antisymm (capacityRegion_subset_informationRegion W)
    (informationRegion_subset_capacityRegion W)

end CapacityAtlas.ConfidentialBroadcast
