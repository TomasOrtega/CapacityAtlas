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

import CapacityAtlasUtil.Metadata
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace CapacityAtlas

/-- A finite memoryless channel, represented by one probability row for each input.

The normalization and nonnegativity fields are shared by every finite channel in
Capacity Atlas. Operational coding definitions live in
`CapacityAtlasForMathlib.InformationTheory.Code`.
-/
@[capacity_shared_api]
structure FiniteChannel (X Y : Type*) [Fintype X] [Fintype Y] where
  transition : X → Y → ℝ
  nonnegative : ∀ x y, 0 ≤ transition x y
  row_sum : ∀ x, ∑ y, transition x y = 1

namespace FiniteChannel

variable {X Y Z : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

@[ext, capacity_shared_api]
theorem ext {W V : FiniteChannel X Y}
    (h : ∀ x y, W.transition x y = V.transition x y) : W = V := by
  cases W with
  | mk w hw hwsum =>
      cases V with
      | mk v hv hvsum =>
          have hwv : w = v := by
            funext x y
            exact h x y
          subst v
          rfl

@[simp, capacity_shared_api]
theorem transition_nonnegative (W : FiniteChannel X Y) (x : X) (y : Y) :
    0 ≤ W.transition x y :=
  W.nonnegative x y

@[simp, capacity_shared_api]
theorem sum_transition (W : FiniteChannel X Y) (x : X) :
    ∑ y, W.transition x y = 1 :=
  W.row_sum x

/-- A stochastic channel with a nonempty input alphabet has a nonempty output alphabet. -/
@[capacity_shared_api]
theorem output_nonempty [Nonempty X] (W : FiniteChannel X Y) : Nonempty Y := by
  cases isEmpty_or_nonempty Y with
  | inr hY => exact hY
  | inl hY =>
      letI : IsEmpty Y := hY
      obtain ⟨x⟩ := ‹Nonempty X›
      have hrow := W.row_sum x
      simp at hrow

/-- The noiseless channel on a finite alphabet. -/
@[capacity_problem "noiseless-q-ary-channel", capacity_shared_api]
def identity (X : Type*) [Fintype X] [DecidableEq X] : FiniteChannel X X where
  transition x y := if x = y then 1 else 0
  nonnegative x y := by
    split <;> positivity
  row_sum x := by
    simp

/-- Serial composition of two finite channels. -/
@[capacity_shared_api]
def comp (V : FiniteChannel Y Z) (W : FiniteChannel X Y) : FiniteChannel X Z where
  transition x z := ∑ y, W.transition x y * V.transition y z
  nonnegative x z := by
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (W.nonnegative _ _) (V.nonnegative _ _)
  row_sum x := by
    calc
      ∑ z, ∑ y, W.transition x y * V.transition y z =
          ∑ y, ∑ z, W.transition x y * V.transition y z := by
            rw [Finset.sum_comm]
      _ = ∑ y, W.transition x y * (∑ z, V.transition y z) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum]
      _ = ∑ y, W.transition x y := by
            apply Finset.sum_congr rfl
            intro y _
            rw [V.row_sum y, mul_one]
      _ = 1 := W.row_sum x

end FiniteChannel

end CapacityAtlas
