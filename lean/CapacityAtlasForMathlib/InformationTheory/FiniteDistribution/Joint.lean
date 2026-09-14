/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {S Y : Type*} [Fintype S] [Fintype Y]

/-- The joint law of a state and an output sampled from its corresponding row. -/
@[capacity_shared_api]
def joint (state : FiniteDistribution S) (rows : S → FiniteDistribution Y) :
    FiniteDistribution (S × Y) where
  probability output := state output.1 * rows output.1 output.2
  nonnegative output := mul_nonneg (state.nonnegative _) ((rows _).nonnegative _)
  sum_probability := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum]

@[simp, capacity_shared_api]
theorem joint_apply (state : FiniteDistribution S) (rows : S → FiniteDistribution Y)
    (output : S × Y) : state.joint rows output = state output.1 * rows output.1 output.2 :=
  rfl

/-- Entropy of a joint law, including states with zero probability. -/
@[capacity_shared_api]
theorem entropy_joint (state : FiniteDistribution S) (rows : S → FiniteDistribution Y) :
    (state.joint rows).entropy = state.entropy + ∑ s, state s * (rows s).entropy := by
  simp [entropy, Fintype.sum_prod_type, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

@[capacity_shared_api]
theorem entropyBits_joint (state : FiniteDistribution S)
    (rows : S → FiniteDistribution Y) :
    (state.joint rows).entropyBits = state.entropyBits +
      ∑ s, state s * (rows s).entropyBits := by
  simp [entropyBits, entropy_joint, add_div, Finset.sum_div, mul_div_assoc]

end FiniteDistribution

end CapacityAtlas
