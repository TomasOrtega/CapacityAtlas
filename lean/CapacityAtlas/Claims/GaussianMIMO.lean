/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianWaterFilling
import CapacityAtlas.Channels.GaussianMIMO

namespace CapacityAtlas.Claims

/-- Real Gaussian MIMO operational capacity under the registered total power constraint. -/
@[capacity_problem "gaussian-mimo-channel", capacity_claim "operational-capacity" 2,
  capacity_statement, capacity_solved]
theorem gaussianMIMO {tx rx : ℕ} (W : Channel.RealGaussianMIMOModel tx rx) :
    Gaussian.mimoCapacity W.channelMatrix W.totalPower W.noiseVariance =
      Gaussian.mimoFormula W.channelMatrix W.totalPower W.noiseVariance := by
  sorry

/-- The covariance supremum is attained by an admissible real positive-semidefinite covariance. -/
@[capacity_problem "gaussian-mimo-channel", capacity_claim "optimizer-attainment" 1,
  capacity_statement, capacity_solved]
theorem gaussianMIMOAttainment {tx rx : ℕ} (W : Channel.RealGaussianMIMOModel tx rx) :
    ∃ Q : Matrix (Fin tx) (Fin tx) ℝ,
      Gaussian.AdmissibleCovariance W.totalPower Q ∧
      Gaussian.logDet W.channelMatrix W.noiseVariance Q =
        Gaussian.mimoFormula W.channelMatrix W.totalPower W.noiseVariance := by
  sorry

/-- A spectral basis and water level produce an optimal covariance, including zero-gain modes. -/
@[capacity_problem "gaussian-mimo-channel", capacity_claim "water-filling-optimizer" 1,
  capacity_statement, capacity_solved]
theorem gaussianMIMOWaterFilling {tx rx : ℕ} (W : Channel.RealGaussianMIMOModel tx rx) :
    ∃ spectrum : Gaussian.MIMOSpectrum W.channelMatrix, ∃ level : ℝ,
      Gaussian.IsWaterLevel spectrum.gain W.totalPower W.noiseVariance level ∧
      Gaussian.AdmissibleCovariance W.totalPower
        (Gaussian.waterFillingCovariance spectrum W.noiseVariance level) ∧
      Gaussian.logDet W.channelMatrix W.noiseVariance
        (Gaussian.waterFillingCovariance spectrum W.noiseVariance level) =
          Gaussian.mimoFormula W.channelMatrix W.totalPower W.noiseVariance ∧
      Gaussian.waterFillingValue spectrum.gain W.noiseVariance level =
        Gaussian.mimoFormula W.channelMatrix W.totalPower W.noiseVariance := by
  sorry

end CapacityAtlas.Claims
