/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlas.Channels.GaussianMIMOBroadcast

namespace CapacityAtlas.Claims

/-- The published private-message capacity equality, stated without assuming its proof. -/
@[capacity_problem "gaussian-mimo-broadcast-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_proposition, capacity_solved]
def gaussianMIMOBroadcast {K tx : ℕ} {rx : Fin K → ℕ}
    (W : Channel.RealGaussianMIMOBroadcastModel K tx rx) : Prop :=
  Gaussian.MIMOBroadcast.capacityRegion W.channelMatrix W.noiseCovariance W.totalPower =
    Gaussian.MIMOBroadcast.region W.channelMatrix W.noiseCovariance W.totalPower

end CapacityAtlas.Claims
