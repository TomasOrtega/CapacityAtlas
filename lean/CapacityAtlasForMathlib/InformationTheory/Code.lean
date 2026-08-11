/-
Copyright 2026 The Capacity Atlas Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannel

open scoped BigOperators

namespace CapacityAtlas

variable {X Y : Type*}
variable [Fintype X] [Fintype Y]

/-- A deterministic one-use code for a fixed finite channel. -/
@[capacity_shared_api]
structure OneShotCode (W : FiniteChannel X Y) (M : Type*) [Fintype M] where
  encode : M → X
  decode : Y → M

namespace OneShotCode

variable {M : Type*} [Fintype M] [DecidableEq M]
variable {W : FiniteChannel X Y}

/-- Probability of correct decoding conditioned on a particular message. -/
@[capacity_shared_api]
def successProbability (code : OneShotCode W M) (message : M) : ℝ :=
  ∑ output, if code.decode output = message then
    W.transition (code.encode message) output
  else
    0

/-- Probability of error conditioned on a particular message. -/
@[capacity_shared_api]
def errorProbability (code : OneShotCode W M) (message : M) : ℝ :=
  1 - code.successProbability message

/-- Average success probability under the uniform message distribution. -/
@[capacity_shared_api]
noncomputable def averageSuccessProbability [Nonempty M] (code : OneShotCode W M) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ message, code.successProbability message

/-- Average error probability under the uniform message distribution. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability [Nonempty M] (code : OneShotCode W M) : ℝ :=
  1 - code.averageSuccessProbability

/-- Conditional error is the channel mass of the outputs decoded incorrectly. -/
@[capacity_shared_api]
theorem errorProbability_eq_sum_decode_ne (code : OneShotCode W M) (message : M) :
    code.errorProbability message =
      ∑ output, if code.decode output ≠ message then
        W.transition (code.encode message) output
      else 0 := by
  unfold errorProbability successProbability
  rw [← W.row_sum (code.encode message), ← Finset.sum_sub_distrib]
  apply Fintype.sum_congr
  intro output
  by_cases hdecode : code.decode output = message <;> simp [hdecode]

/-- Average error is the uniform average of the conditional errors. -/
@[capacity_shared_api]
theorem averageErrorProbability_eq [Nonempty M] (code : OneShotCode W M) :
    code.averageErrorProbability =
      (Fintype.card M : ℝ)⁻¹ * ∑ message, code.errorProbability message := by
  have hcard : (Fintype.card M : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold averageErrorProbability averageSuccessProbability errorProbability
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end OneShotCode

end CapacityAtlas
