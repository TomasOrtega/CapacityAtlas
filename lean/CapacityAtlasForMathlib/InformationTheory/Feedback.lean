/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators

namespace CapacityAtlas.Feedback

attribute [local instance] Classical.propDecidable

/-- A channel input depends only on the outputs strictly preceding its time index. -/
@[capacity_shared_api]
abbrev Policy (X Y : Type*) (n : ℕ) :=
  (i : Fin n) → (Fin i.val → Y) → X

namespace Policy

variable {X Y : Type*} {n : ℕ}

@[capacity_shared_api]
noncomputable instance instFintype [Fintype X] [Fintype Y] : Fintype (Policy X Y n) :=
  inferInstanceAs (Fintype ((i : Fin n) → (Fin i.val → Y) → X))

/-- Evaluate the policy on the strict prefix of a complete output word. -/
@[capacity_shared_api]
def input (policy : Policy X Y n) (outputs : Fin n → Y) (i : Fin n) : X :=
  policy i (fun j ↦ outputs (Fin.castLE (Nat.le_of_lt i.isLt) j))

/-- An ordinary input word ignores every feedback observation. -/
@[capacity_shared_api]
def ofWord (word : Fin n → X) : Policy X Y n := fun i _ ↦ word i

@[simp, capacity_shared_api]
theorem input_ofWord (word : Fin n → X) (outputs : Fin n → Y) (i : Fin n) :
    (ofWord word).input outputs i = word i := rfl

/-- Restrict a policy to its first `n` uses. -/
@[capacity_shared_api]
def init (policy : Policy X Y (n + 1)) : Policy X Y n :=
  fun i ↦ policy i.castSucc

@[simp, capacity_shared_api]
theorem input_init (policy : Policy X Y (n + 1)) (outputs : Fin (n + 1) → Y)
    (i : Fin n) : policy.init.input (Fin.init outputs) i = policy.input outputs i.castSucc :=
  rfl

@[simp, capacity_shared_api]
theorem input_snoc_castSucc (policy : Policy X Y (n + 1)) (outputs : Fin n → Y)
    (output : Y) (i : Fin n) :
    policy.input (Fin.snoc outputs output) i.castSucc = policy.init.input outputs i := by
  rw [← input_init, Fin.init_snoc]

@[simp, capacity_shared_api]
theorem input_last (policy : Policy X Y (n + 1)) (outputs : Fin (n + 1) → Y) :
    policy.input outputs (Fin.last n) = policy (Fin.last n) (Fin.init outputs) := rfl

@[simp, capacity_shared_api]
theorem input_snoc_last (policy : Policy X Y (n + 1)) (outputs : Fin n → Y)
    (output : Y) :
    policy.input (Fin.snoc outputs output) (Fin.last n) = policy (Fin.last n) outputs := by
  rw [input_last, Fin.init_snoc]

end Policy

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The physical output-word mass induced by a deterministic feedback policy. -/
@[capacity_shared_api]
def blockMass (channel : FiniteChannel X Y) {n : ℕ} (policy : Policy X Y n)
    (outputs : Fin n → Y) : ℝ :=
  ∏ i, channel.transition (policy.input outputs i) (outputs i)

@[capacity_shared_api]
theorem blockMass_nonnegative (channel : FiniteChannel X Y) {n : ℕ}
    (policy : Policy X Y n) (outputs : Fin n → Y) : 0 ≤ blockMass channel policy outputs :=
  Finset.prod_nonneg fun _ _ ↦ channel.nonnegative _ _

/-- The final input depends on the preceding outputs but not on the final output. -/
@[capacity_shared_api]
theorem blockMass_snoc (channel : FiniteChannel X Y) {n : ℕ}
    (policy : Policy X Y (n + 1)) (outputs : Fin n → Y) (output : Y) :
    blockMass channel policy (Fin.snoc outputs output) =
      blockMass channel policy.init outputs *
        channel.transition (policy (Fin.last n) outputs) output := by
  simp only [blockMass, Fin.prod_univ_castSucc, Policy.input_snoc_castSucc,
    Fin.snoc_castSucc, Policy.input_snoc_last, Fin.snoc_last]

@[capacity_shared_api]
theorem sum_blockMass (channel : FiniteChannel X Y) (n : ℕ) (policy : Policy X Y n) :
    ∑ outputs, blockMass channel policy outputs = 1 := by
  classical
  induction n with
  | zero => simp [blockMass]
  | succ n ih =>
      rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ Y)).sum_comp]
      simp only [Fintype.sum_prod_type, Fin.snocEquiv, Equiv.coe_fn_mk, blockMass_snoc]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, FiniteChannel.sum_transition, mul_one]
      exact ih policy.init

/-- The finite channel from a feedback policy to its full output word. -/
@[capacity_shared_api]
noncomputable def blockChannel (channel : FiniteChannel X Y) (n : ℕ) :
    FiniteChannel (Policy X Y n) (Fin n → Y) where
  transition := blockMass channel
  nonnegative := blockMass_nonnegative channel
  row_sum := sum_blockMass channel n

@[simp, capacity_shared_api]
theorem blockChannel_transition (channel : FiniteChannel X Y) (n : ℕ)
    (policy : Policy X Y n) (outputs : Fin n → Y) :
    (blockChannel channel n).transition policy outputs =
      ∏ i, channel.transition (policy.input outputs i) (outputs i) := rfl

@[capacity_shared_api]
theorem blockChannel_transition_snoc (channel : FiniteChannel X Y) {n : ℕ}
    (policy : Policy X Y (n + 1)) (outputs : Fin n → Y) (output : Y) :
    (blockChannel channel (n + 1)).transition policy (Fin.snoc outputs output) =
      (blockChannel channel n).transition policy.init outputs *
        channel.transition (policy (Fin.last n) outputs) output :=
  blockMass_snoc channel policy outputs output

/-- Ignoring the output history recovers the ordinary memoryless block law exactly. -/
@[capacity_shared_api]
theorem blockChannel_transition_ofWord (channel : FiniteChannel X Y) (n : ℕ)
    (word : Fin n → X) (outputs : Fin n → Y) :
    (blockChannel channel n).transition (Policy.ofWord word) outputs =
      (channel.block n).transition word outputs := rfl

/-- A fixed-length deterministic code with strictly causal noiseless output feedback. -/
@[capacity_shared_api]
structure BlockCode (channel : FiniteChannel X Y) (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  encode : Fin messageCount → Policy X Y blocklength
  decode : (Fin blocklength → Y) → Fin messageCount

namespace BlockCode

variable {channel : FiniteChannel X Y} {blocklength : ℕ}

/-- Interpret the code as a one-shot code for its actual adaptive block channel. -/
@[capacity_shared_api]
def toOneShotCode (code : BlockCode channel blocklength) :
    OneShotCode (blockChannel channel blocklength) (Fin code.messageCount) where
  encode := code.encode
  decode := code.decode

/-- Average decoding error under uniform messages and the induced feedback law. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability (code : BlockCode channel blocklength) : ℝ :=
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  code.toOneShotCode.averageErrorProbability

/-- Rate in bits per physical channel use. -/
@[capacity_shared_api]
noncomputable def rate (code : BlockCode channel blocklength) : ℝ :=
  Real.logb 2 code.messageCount / blocklength

/-- Implement an ordinary code by ignoring all feedback observations. -/
@[capacity_shared_api]
def ofOrdinaryCode (code : FiniteChannel.BlockCode channel blocklength) :
    BlockCode channel blocklength where
  messageCount := code.messageCount
  messageCount_pos := code.messageCount_pos
  encode message := Policy.ofWord (code.encode message)
  decode := code.decode

@[simp, capacity_shared_api]
theorem ofOrdinaryCode_messageCount (code : FiniteChannel.BlockCode channel blocklength) :
    (ofOrdinaryCode code).messageCount = code.messageCount := rfl

@[simp, capacity_shared_api]
theorem ofOrdinaryCode_rate (code : FiniteChannel.BlockCode channel blocklength) :
    (ofOrdinaryCode code).rate = code.rate := rfl

@[simp, capacity_shared_api]
theorem ofOrdinaryCode_averageErrorProbability
    (code : FiniteChannel.BlockCode channel blocklength) :
    (ofOrdinaryCode code).averageErrorProbability = code.averageErrorProbability := by
  simp only [averageErrorProbability, FiniteChannel.BlockCode.averageErrorProbability,
    OneShotCode.averageErrorProbability, OneShotCode.averageSuccessProbability,
    OneShotCode.successProbability, toOneShotCode, FiniteChannel.BlockCode.toOneShotCode,
    ofOrdinaryCode, blockChannel_transition_ofWord]
  rfl

end BlockCode

/-- Reliable deterministic feedback coding at every sufficiently large blocklength. -/
@[capacity_shared_api]
def AchievableRate (channel : FiniteChannel X Y) (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ firstBlocklength : ℕ, 0 < firstBlocklength ∧
    ∀ blocklength, firstBlocklength ≤ blocklength →
      ∃ code : BlockCode channel blocklength,
        code.averageErrorProbability ≤ ε ∧ rate ≤ code.rate

/-- Average-error feedback capacity in bits per channel use. -/
@[capacity_shared_api]
noncomputable def operationalCapacityBits (channel : FiniteChannel X Y) : ℝ :=
  sSup {rate | AchievableRate channel rate}

/-- Any rate achievable without feedback remains achievable with feedback. -/
@[capacity_shared_api]
theorem achievableRate_of_ordinary {channel : FiniteChannel X Y} {rate : ℝ}
    (hrate : channel.AchievableRate rate) : AchievableRate channel rate := by
  intro ε hε
  obtain ⟨first, hfirst, hcodes⟩ := hrate ε hε
  refine ⟨first, hfirst, ?_⟩
  intro n hn
  obtain ⟨code, herror, hcodeRate⟩ := hcodes n hn
  exact ⟨BlockCode.ofOrdinaryCode code, by simpa using herror, by simpa using hcodeRate⟩

end CapacityAtlas.Feedback
