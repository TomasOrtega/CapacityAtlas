/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcastRegion

namespace CapacityAtlas.Channel

/-- Fixed real MIMO broadcast channel with message-averaged total transmit power. -/
@[capacity_problem "gaussian-mimo-broadcast-channel", capacity_definition]
structure RealGaussianMIMOBroadcastModel (K tx : ℕ) (rx : Fin K → ℕ) where
  receivers_ge_two : 2 ≤ K
  transmitAntennas_pos : 0 < tx
  receiveAntennas_pos : ∀ i, 0 < rx i
  channelMatrix : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ
  noiseCovariance : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ
  noiseCovariance_posDef : ∀ i, (noiseCovariance i).PosDef
  totalPower : ℝ
  totalPower_nonnegative : 0 ≤ totalPower

end CapacityAtlas.Channel
