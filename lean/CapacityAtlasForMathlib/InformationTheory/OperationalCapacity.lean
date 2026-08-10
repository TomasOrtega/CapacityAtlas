/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.Code
import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The memoryless `n`-fold extension of a finite channel. -/
@[capacity_shared_api]
def block (channel : FiniteChannel X Y) (n : ℕ) :
    FiniteChannel (Fin n → X) (Fin n → Y) where
  transition input output := ∏ i, channel.transition (input i) (output i)
  nonnegative input output := Finset.prod_nonneg fun i _ ↦
    channel.nonnegative (input i) (output i)
  row_sum input := by
    rw [← Fintype.prod_sum]
    simp

@[simp, capacity_shared_api]
theorem block_transition (channel : FiniteChannel X Y) (n : ℕ)
    (input : Fin n → X) (output : Fin n → Y) :
    (channel.block n).transition input output =
      ∏ i, channel.transition (input i) (output i) :=
  rfl

/-- A deterministic block code with a positive finite message set. -/
@[capacity_shared_api]
structure BlockCode (channel : FiniteChannel X Y) (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  encode : Fin messageCount → Fin blocklength → X
  decode : (Fin blocklength → Y) → Fin messageCount

namespace BlockCode

variable {channel : FiniteChannel X Y} {blocklength : ℕ}

/-- A block code viewed as a one-shot code for the product channel. -/
@[capacity_shared_api]
def toOneShotCode (code : BlockCode channel blocklength) :
    OneShotCode (channel.block blocklength) (Fin code.messageCount) where
  encode := code.encode
  decode := code.decode

/-- Average decoding error under the uniform message distribution. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability (code : BlockCode channel blocklength) : ℝ :=
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  code.toOneShotCode.averageErrorProbability

/-- Code rate in bits per channel use. -/
@[capacity_shared_api]
noncomputable def rate (code : BlockCode channel blocklength) : ℝ :=
  Real.logb 2 code.messageCount / blocklength

end BlockCode

/-- A rate achievable by deterministic block codes with vanishing average error. -/
@[capacity_shared_api]
def AchievableRate (channel : FiniteChannel X Y) (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ firstBlocklength : ℕ, 0 < firstBlocklength ∧
    ∀ blocklength, firstBlocklength ≤ blocklength →
      ∃ code : BlockCode channel blocklength,
        code.averageErrorProbability ≤ ε ∧ rate ≤ code.rate

/-- Operational average-error capacity in bits per channel use. -/
@[capacity_shared_api]
noncomputable def operationalCapacityBits (channel : FiniteChannel X Y) : ℝ :=
  sSup {rate | channel.AchievableRate rate}

/-- The finite-channel coding theorem for a particular channel. -/
@[capacity_shared_api]
def SatisfiesCodingTheorem (channel : FiniteChannel X Y) : Prop :=
  channel.operationalCapacityBits = channel.informationCapacityBits

@[capacity_shared_api]
theorem operationalCapacityBits_eq_of_satisfiesCodingTheorem
    (channel : FiniteChannel X Y) (capacity : ℝ)
    (codingTheorem : channel.SatisfiesCodingTheorem)
    (informationCapacity : channel.informationCapacityBits = capacity) :
    channel.operationalCapacityBits = capacity :=
  codingTheorem.trans informationCapacity

end FiniteChannel

end CapacityAtlas
