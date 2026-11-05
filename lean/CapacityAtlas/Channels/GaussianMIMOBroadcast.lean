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
  /-- The broadcast model has at least two receivers. -/
  receivers_ge_two : 2 ≤ K
  /-- The transmitter has at least one antenna. -/
  transmitAntennas_pos : 0 < tx
  /-- Each receiver has at least one antenna. -/
  receiveAntennas_pos : ∀ i, 0 < rx i
  /-- Linear map from transmit antennas to each receiver's antenna coordinates. -/
  channelMatrix : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ
  /-- Noise covariance matrix at each receiver. -/
  noiseCovariance : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ
  /-- Each receiver's noise covariance is positive definite. -/
  noiseCovariance_posDef : ∀ i, (noiseCovariance i).PosDef
  /-- Total transmit-power budget, averaged over messages and channel uses. -/
  totalPower : ℝ
  /-- The total transmit-power budget is nonnegative. -/
  totalPower_nonnegative : 0 ≤ totalPower

end CapacityAtlas.Channel
