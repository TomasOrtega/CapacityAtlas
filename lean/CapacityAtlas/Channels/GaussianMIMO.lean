/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace CapacityAtlas.Channel

open CapacityAtlas

/-- A real Gaussian MIMO channel with total block-average power for every message
and white-noise variance. The operational code applies the budget across all transmit antennas. -/
@[capacity_problem "gaussian-mimo-channel", capacity_definition]
structure RealGaussianMIMOModel (transmitAntennas receiveAntennas : ℕ) where
  /-- Linear map from transmit-antenna coordinates to receive-antenna coordinates. -/
  channelMatrix : Matrix (Fin receiveAntennas) (Fin transmitAntennas) ℝ
  /-- Variance of white Gaussian noise in each receive coordinate. -/
  noiseVariance : ℝ
  /-- The white-noise variance is strictly positive. -/
  noiseVariance_pos : 0 < noiseVariance
  /-- Total block-average transmit-power budget required for every message. -/
  totalPower : ℝ
  /-- The total transmit-power budget is nonnegative. -/
  totalPower_nonnegative : 0 ≤ totalPower

end CapacityAtlas.Channel
