/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianFiniteInputs

namespace CapacityAtlas.Claims

/-- Amplitude-constrained AWGN capacity is attained by a finite-support input law. -/
@[capacity_problem "amplitude-constrained-gaussian-channel", capacity_claim "operational-capacity" 1,
  capacity_statement, capacity_solved]
theorem amplitudeGaussian (A N : ℝ) (hA : 0 ≤ A) (hN : 0 < N) :
    Gaussian.amplitudeCapacity A N = Gaussian.amplitudeFormula A N ∧
      ∃ k : ℕ, ∃ p : FiniteDistribution (Fin k), ∃ location : Fin k → ℝ,
        (∀ i, |location i| ≤ A) ∧
        Gaussian.mutualInformation (Gaussian.finiteInput p location) N =
          Gaussian.amplitudeCapacity A N ∧
        Gaussian.amplitudeCapacity A N ≤ Gaussian.awgnFormula (A ^ 2) N := by
  sorry

/-- The peak-amplitude operational capacity equals the compact-input information supremum. -/
@[capacity_problem "amplitude-constrained-gaussian-channel", capacity_claim "capacity-formula" 1,
  capacity_statement, capacity_solved]
theorem amplitudeGaussianCapacity (A N : ℝ) (hA : 0 ≤ A) (hN : 0 < N) :
    Gaussian.amplitudeCapacity A N = Gaussian.amplitudeFormula A N := by
  sorry

/-- A finite-support input attains the operational peak-amplitude capacity. -/
@[capacity_problem "amplitude-constrained-gaussian-channel", capacity_claim "finite-support-attainment" 1,
  capacity_statement, capacity_solved]
theorem amplitudeGaussianAttainment (A N : ℝ) (hA : 0 ≤ A) (hN : 0 < N) :
    ∃ k : ℕ, ∃ p : FiniteDistribution (Fin k), ∃ location : Fin k → ℝ,
      (∀ i, |location i| ≤ A) ∧
      Gaussian.mutualInformation (Gaussian.finiteInput p location) N =
        Gaussian.amplitudeCapacity A N := by
  sorry

/-- Peak-amplitude capacity is bounded above by the relaxed average-power formula. -/
@[capacity_problem "amplitude-constrained-gaussian-channel", capacity_claim "power-relaxation-converse" 1,
  capacity_statement, capacity_solved]
theorem amplitudeGaussianUpper (A N : ℝ) (hA : 0 ≤ A) (hN : 0 < N) :
    Gaussian.amplitudeCapacity A N ≤ Gaussian.awgnFormula (A ^ 2) N := by
  sorry

end CapacityAtlas.Claims
