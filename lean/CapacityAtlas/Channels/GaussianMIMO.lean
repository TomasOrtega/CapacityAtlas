/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalTheory
import Mathlib.Data.Matrix.Basic

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

/-- Real-channel normalization uses `1/2 log₂ det`; the value argument is the water-filling optimum. -/
@[capacity_problem "gaussian-mimo-channel", capacity_statement]
def gaussianMIMOCapacityStatement (transmitAntennas receiveAntennas : ℕ)
    (theory : ScalarOperationalTheory
      (RealGaussianMIMOModel transmitAntennas receiveAntennas))
    (waterFillingLogDetValue :
      RealGaussianMIMOModel transmitAntennas receiveAntennas → ℝ)
    (channel : RealGaussianMIMOModel transmitAntennas receiveAntennas) : Prop :=
  theory.capacity channel = waterFillingLogDetValue channel

end CapacityAtlas.Channel
