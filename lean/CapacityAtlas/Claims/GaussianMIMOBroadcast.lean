/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlas.Channels.GaussianMIMOBroadcast
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Achievability
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Converse

namespace CapacityAtlas.Claims

/-- Private-message capacity equals the closed convex Gaussian dirty-paper region. -/
@[capacity_problem "gaussian-mimo-broadcast-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved, capacity_formal_proof]
theorem gaussianMIMOBroadcast {K tx : ℕ} {rx : Fin K → ℕ}
    (W : Channel.RealGaussianMIMOBroadcastModel K tx rx) :
  Gaussian.MIMOBroadcast.capacityRegion W.channelMatrix W.noiseCovariance W.totalPower =
    Gaussian.MIMOBroadcast.region W.channelMatrix W.noiseCovariance W.totalPower := by
  apply Set.Subset.antisymm
  · exact Gaussian.MIMOBroadcast.capacityRegion_subset_region _ _ W.noiseCovariance_posDef
      (lt_of_lt_of_le (by decide : 0 < 2) W.receivers_ge_two)
      W.transmitAntennas_pos W.totalPower_nonnegative
  · exact Gaussian.MIMOBroadcast.region_subset_capacityRegion _ _ W.noiseCovariance_posDef
      W.totalPower_nonnegative

end CapacityAtlas.Claims
