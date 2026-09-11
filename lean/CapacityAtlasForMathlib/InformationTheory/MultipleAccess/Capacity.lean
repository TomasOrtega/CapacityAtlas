/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasMAC, commit ec5be554b9644df94dd58190963793f3f1d1da52,
CapacityAtlasMAC.lean. Imports and certificate types use the monorepo modules.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess.Converse
import CapacityAtlasForMathlib.InformationTheory.MultipleAccess.ProductCoding
import CapacityAtlasForMathlib.InformationTheory.MultipleAccess.TimeSharing

namespace CapacityAtlasMAC

open CapacityAtlas MultipleAccess

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- Every finite time-sharing witness yields separate deterministic MAC codes. -/
theorem informationRegion_subset_operationalRegion (W : FiniteChannel (X₁ × X₂) Y) :
    informationRegion W ⊆ operationalRegion W := by
  classical
  rintro r ⟨hr₁, hr₂, k, weights, p₁, p₂, ha, hb, hc⟩
  apply achievableRate_of_timeSharing W weights
  apply achievableRate_of_productInput (timeSharingChannel W weights)
    (FiniteDistribution.productFamily p₁) (FiniteDistribution.productFamily p₂) r hr₁ hr₂
  · simpa only [leftInformation_timeSharing] using ha
  · simpa only [rightInformation_timeSharing] using hb
  · simpa only [jointInformation_timeSharing] using hc

/-- The full MAC region, including its boundary and zero-rate axes. -/
theorem capacityRegion (W : FiniteChannel (X₁ × X₂) Y) :
    operationalRegion W = informationRegion W :=
  Set.Subset.antisymm (operationalRegion_subset_informationRegion W)
    (informationRegion_subset_operationalRegion W)

end CapacityAtlasMAC
