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

/-- A real Gaussian MIMO channel with total input power and white-noise variance. -/
@[capacity_problem "gaussian-mimo-channel", capacity_definition]
structure RealGaussianMIMOModel (transmitAntennas receiveAntennas : ℕ) where
  channelMatrix : Matrix (Fin receiveAntennas) (Fin transmitAntennas) ℝ
  noiseVariance : ℝ
  noiseVariance_pos : 0 < noiseVariance
  totalPower : ℝ
  totalPower_nonnegative : 0 ≤ totalPower

end CapacityAtlas.Channel
