/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteProductDistribution
import CapacityAtlasForMathlib.InformationTheory.SequentialInformation

open scoped BigOperators

namespace CapacityAtlas

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq Z]

namespace FiniteChannel

/-- Output observations commute with memoryless block extension. -/
@[capacity_shared_api]
theorem block_relabelOutput (channel : FiniteChannel X Y) (f : Y → Z) (n : ℕ) :
    (channel.relabelOutput f).block n =
      (channel.block n).relabelOutput (fun word i ↦ f (word i)) := by
  classical
  ext input output
  have h := congrArg (fun distribution : FiniteDistribution (Fin n → Z) ↦ distribution output)
    (FiniteDistribution.map_productFamily
      (fun i ↦ channel.rowDistribution (input i)) (fun _ ↦ f))
  exact h.symm

/-- An output observable has the same expectation before and after relabeling. -/
@[capacity_shared_api]
theorem sum_relabelOutput_transition_mul (channel : FiniteChannel X Y) (f : Y → Z)
    (input : X) (observable : Z → ℝ) :
    ∑ z, (channel.relabelOutput f).transition input z * observable z =
      ∑ y, channel.transition input y * observable (f y) :=
  (channel.rowDistribution input).sum_map_mul f observable

end FiniteChannel

namespace OneShotCode

variable {M : Type*} [Fintype M] {channel : FiniteChannel X Y} {f : Y → Z}

/-- Decode an observed output by first applying its observation map. -/
@[capacity_shared_api]
def pullbackOutput (code : OneShotCode (channel.relabelOutput f) M) :
    OneShotCode channel M where
  encode := code.encode
  decode y := code.decode (f y)

@[simp, capacity_shared_api]
theorem pullbackOutput_encode (code : OneShotCode (channel.relabelOutput f) M) :
    code.pullbackOutput.encode = code.encode := rfl

@[simp, capacity_shared_api]
theorem pullbackOutput_decode (code : OneShotCode (channel.relabelOutput f) M) (y : Y) :
    code.pullbackOutput.decode y = code.decode (f y) := rfl

@[simp, capacity_shared_api]
theorem errorProbability_pullbackOutput [DecidableEq M]
    (code : OneShotCode (channel.relabelOutput f) M) (message : M) :
    code.pullbackOutput.errorProbability message = code.errorProbability message := by
  rw [errorProbability_eq_sum_decode_ne, errorProbability_eq_sum_decode_ne]
  simpa only [pullbackOutput_encode, pullbackOutput_decode, mul_ite, mul_one, mul_zero] using
    (channel.sum_relabelOutput_transition_mul f (code.encode message)
      (fun z ↦ if code.decode z ≠ message then 1 else 0)).symm

@[simp, capacity_shared_api]
theorem averageErrorProbability_pullbackOutput [DecidableEq M] [Nonempty M]
    (code : OneShotCode (channel.relabelOutput f) M) :
    code.pullbackOutput.averageErrorProbability = code.averageErrorProbability := by
  simp only [averageErrorProbability_eq, errorProbability_pullbackOutput]

end OneShotCode

namespace FiniteChannel.BlockCode

variable {channel : FiniteChannel X Y} {f : Y → Z} {n : ℕ}

/-- Apply the output observation at every coordinate before decoding. -/
@[capacity_shared_api]
def pullbackOutput (code : BlockCode (channel.relabelOutput f) n) : BlockCode channel n where
  messageCount := code.messageCount
  messageCount_pos := code.messageCount_pos
  encode := code.encode
  decode word := code.decode (fun i ↦ f (word i))

@[simp, capacity_shared_api]
theorem pullbackOutput_messageCount (code : BlockCode (channel.relabelOutput f) n) :
    code.pullbackOutput.messageCount = code.messageCount := rfl

@[simp, capacity_shared_api]
theorem pullbackOutput_encode (code : BlockCode (channel.relabelOutput f) n) :
    code.pullbackOutput.encode = code.encode := rfl

@[simp, capacity_shared_api]
theorem pullbackOutput_decode (code : BlockCode (channel.relabelOutput f) n)
    (word : Fin n → Y) :
    code.pullbackOutput.decode word = code.decode (fun i ↦ f (word i)) := rfl

@[simp, capacity_shared_api]
theorem rate_pullbackOutput (code : BlockCode (channel.relabelOutput f) n) :
    code.pullbackOutput.rate = code.rate := rfl

@[simp, capacity_shared_api]
theorem averageErrorProbability_pullbackOutput
    (code : BlockCode (channel.relabelOutput f) n) :
    code.pullbackOutput.averageErrorProbability = code.averageErrorProbability := by
  classical
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  letI : Nonempty (Fin code.pullbackOutput.messageCount) :=
    Fin.pos_iff_nonempty.mp code.pullbackOutput.messageCount_pos
  unfold averageErrorProbability
  rw [OneShotCode.averageErrorProbability_eq, OneShotCode.averageErrorProbability_eq]
  congr 1
  apply Fintype.sum_congr
  intro message
  rw [OneShotCode.errorProbability_eq_sum_decode_ne,
    OneShotCode.errorProbability_eq_sum_decode_ne]
  change (∑ word, if code.decode (fun i ↦ f (word i)) ≠ message then
    (channel.block n).transition (code.encode message) word else 0) =
      ∑ word, if code.decode word ≠ message then
        ((channel.relabelOutput f).block n).transition (code.encode message) word else 0
  rw [block_relabelOutput]
  simpa only [mul_ite, mul_one, mul_zero] using
    ((channel.block n).sum_relabelOutput_transition_mul (fun word i ↦ f (word i))
      (code.encode message) (fun word ↦ if code.decode word ≠ message then 1 else 0)).symm

end FiniteChannel.BlockCode

end CapacityAtlas
