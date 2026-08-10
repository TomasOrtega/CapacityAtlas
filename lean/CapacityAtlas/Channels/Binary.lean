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

namespace CapacityAtlas.Channel

open CapacityAtlas

/-- Transition probabilities of the binary symmetric channel. -/
def binarySymmetricTransition (p : ℝ) (input output : Bool) : ℝ :=
  if input = output then 1 - p else p

/-- The binary symmetric channel with crossover probability `p`. -/
@[capacity_problem "binary-symmetric-channel", capacity_definition]
def binarySymmetric (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteChannel Bool Bool where
  transition := binarySymmetricTransition p
  nonnegative input output := by
    simp only [binarySymmetricTransition]
    split
    · linarith
    · exact hp0
  row_sum input := by
    cases input <;> simp [binarySymmetricTransition]

/-- At crossover probability zero, the binary symmetric channel is noiseless. -/
@[capacity_problem "binary-symmetric-channel", capacity_short_proof]
theorem binarySymmetric_zero :
    binarySymmetric 0 (by norm_num) (by norm_num) =
      FiniteChannel.identity Bool := by
  apply FiniteChannel.ext
  intro input output
  simp [binarySymmetric, binarySymmetricTransition, FiniteChannel.identity]

/-- Transition probabilities of the binary erasure channel.

`none` is the erasure symbol and `some bit` is an unerased output.
-/
def binaryErasureTransition (e : ℝ) (input : Bool) : Option Bool → ℝ
  | none => e
  | some output => if input = output then 1 - e else 0

/-- The binary erasure channel with erasure probability `e`. -/
@[capacity_problem "binary-erasure-channel", capacity_definition]
def binaryErasure (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    FiniteChannel Bool (Option Bool) where
  transition := binaryErasureTransition e
  nonnegative input output := by
    cases output with
    | none => exact he0
    | some output =>
        simp only [binaryErasureTransition]
        split
        · linarith
        · norm_num
  row_sum input := by
    cases input <;> simp [binaryErasureTransition]

/-- Transition probabilities of the binary Z-channel.

Input `false` is transmitted without error. Input `true` changes to `false`
with probability `p`.
-/
def binaryZTransition (p : ℝ) (input output : Bool) : ℝ :=
  match input, output with
  | false, false => 1
  | false, true => 0
  | true, false => p
  | true, true => 1 - p

/-- The binary Z-channel with crossover probability `p`. -/
@[capacity_problem "binary-z-channel", capacity_definition]
def binaryZ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteChannel Bool Bool where
  transition := binaryZTransition p
  nonnegative input output := by
    cases input <;> cases output <;> simp [binaryZTransition] <;> linarith
  row_sum input := by
    cases input <;> simp [binaryZTransition]

end CapacityAtlas.Channel
