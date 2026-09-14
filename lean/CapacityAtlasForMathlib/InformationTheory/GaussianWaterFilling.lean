/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational

open scoped BigOperators

namespace CapacityAtlas.Gaussian

/-- Squared singular gains and an orthogonal transmit basis for a fixed real matrix.
Existence is not assumed by a channel model. The water-filling claim supplies a witness. -/
structure MIMOSpectrum {tx rx : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ) where
  basis : Matrix (Fin tx) (Fin tx) ℝ
  orthogonal : basis.transpose * basis = 1
  gain : Fin tx → ℝ
  gain_nonnegative : ∀ k, 0 ≤ gain k
  gram : H.transpose * H = basis * Matrix.diagonal gain * basis.transpose

/-- Allocate no power to a zero-gain mode, avoiding totalized division by zero. -/
noncomputable def waterFillingPower {tx : ℕ} (gain : Fin tx → ℝ)
    (N level : ℝ) (k : Fin tx) : ℝ :=
  if 0 < gain k then max 0 (level - N / gain k) else 0

/-- The budget is exhausted if any mode has positive gain. For a zero channel,
all powers are zero and unused budget is permitted, including empty dimensions. -/
def IsWaterLevel {tx : ℕ} (gain : Fin tx → ℝ) (P N level : ℝ) : Prop :=
  0 ≤ level ∧ (∑ k, waterFillingPower gain N level k) ≤ P ∧
    ((∃ k, 0 < gain k) → (∑ k, waterFillingPower gain N level k) = P)

noncomputable def waterFillingCovariance {tx rx : ℕ}
    {H : Matrix (Fin rx) (Fin tx) ℝ} (spectrum : MIMOSpectrum H)
    (N level : ℝ) : Matrix (Fin tx) (Fin tx) ℝ :=
  spectrum.basis * Matrix.diagonal (waterFillingPower spectrum.gain N level) *
    spectrum.basis.transpose

/-- Bits per real vector channel use, including the real-channel one-half factor. -/
noncomputable def waterFillingValue {tx : ℕ} (gain : Fin tx → ℝ) (N level : ℝ) : ℝ :=
  ∑ k, awgnFormula (gain k * waterFillingPower gain N level k) N

end CapacityAtlas.Gaussian
