/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.DecoderSideInformation
import CapacityAtlasForMathlib.InformationTheory.FiniteMixture
import CapacityAtlasForMathlib.InformationTheory.FiniteProductProbability
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators

namespace CapacityAtlas.CausalState

attribute [local instance] Classical.propDecidable

/-- An input at time `i` may depend on the states through time `i`, but not outputs. -/
@[capacity_shared_api]
abbrev Policy (S X : Type*) (n : ℕ) :=
  (i : Fin n) → (Fin (i.val + 1) → S) → X

namespace Policy

variable {S X : Type*} {n : ℕ}

@[capacity_shared_api]
noncomputable instance instFintype [Fintype S] [Fintype X] : Fintype (Policy S X n) :=
  inferInstanceAs (Fintype ((i : Fin n) → (Fin (i.val + 1) → S) → X))

/-- Evaluate a policy on the available prefix of a full state word. -/
@[capacity_shared_api]
def input (policy : Policy S X n) (states : Fin n → S) (i : Fin n) : X :=
  policy i (fun j ↦ states (Fin.castLE (Nat.succ_le_of_lt i.isLt) j))

/-- A word of Shannon strategies uses only the current state at each time. -/
@[capacity_shared_api]
def ofStrategies (strategies : Fin n → S → X) : Policy S X n :=
  fun i history ↦ strategies i (history (Fin.last i.val))

@[simp, capacity_shared_api]
theorem input_ofStrategies (strategies : Fin n → S → X) (states : Fin n → S)
    (i : Fin n) : (ofStrategies strategies).input states i = strategies i (states i) :=
  rfl

/-- Restrict a policy to its first `n` uses. -/
@[capacity_shared_api]
def init (policy : Policy S X (n + 1)) : Policy S X n :=
  fun i ↦ policy i.castSucc

@[simp, capacity_shared_api]
theorem input_init (policy : Policy S X (n + 1)) (states : Fin (n + 1) → S)
    (i : Fin n) : policy.init.input (Fin.init states) i = policy.input states i.castSucc :=
  rfl

@[simp, capacity_shared_api]
theorem input_snoc_castSucc (policy : Policy S X (n + 1)) (states : Fin n → S)
    (state : S) (i : Fin n) :
    policy.input (Fin.snoc states state) i.castSucc = policy.init.input states i := by
  rw [← input_init, Fin.init_snoc]

@[simp, capacity_shared_api]
theorem input_last (policy : Policy S X (n + 1)) (states : Fin (n + 1) → S) :
    policy.input states (Fin.last n) = policy (Fin.last n) states := by
  rfl

end Policy

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

/-- The current state is averaged out after evaluating the chosen Shannon strategy. -/
@[capacity_shared_api]
noncomputable def strategyChannel (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) : FiniteChannel (S → X) Y :=
  FiniteChannel.ofRows fun strategy ↦
    state.mixture (fun s ↦ (channels s).rowDistribution (strategy s))

@[simp, capacity_shared_api]
theorem strategyChannel_transition (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (strategy : S → X) (output : Y) :
    (strategyChannel state channels).transition strategy output =
      ∑ s, state s * (channels s).transition (strategy s) output :=
  rfl

/-- The iid-state block law of a causal policy, with only outputs revealed to the decoder. -/
@[capacity_shared_api]
noncomputable def blockChannel (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ) :
    FiniteChannel (Policy S X n) (Fin n → Y) where
  transition policy outputs := ∑ states : Fin n → S,
    (∏ i, state (states i)) *
      ∏ i, (channels (states i)).transition (policy.input states i) (outputs i)
  nonnegative policy outputs := Finset.sum_nonneg fun states _ ↦
    mul_nonneg (Finset.prod_nonneg fun i _ ↦ state.nonnegative (states i))
      (Finset.prod_nonneg fun i _ ↦ (channels (states i)).nonnegative _ _)
  row_sum policy := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← Fintype.prod_sum]
    simp [← Fintype.prod_sum]

@[simp, capacity_shared_api]
theorem blockChannel_transition (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ) (policy : Policy S X n)
    (outputs : Fin n → Y) :
    (blockChannel state channels n).transition policy outputs =
      ∑ states : Fin n → S, (∏ i, state (states i)) *
        ∏ i, (channels (states i)).transition (policy.input states i) (outputs i) :=
  rfl

/-- Memoryless strategies induce exactly the ordinary product strategy channel. -/
@[capacity_shared_api]
theorem blockChannel_transition_ofStrategies (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ) (strategies : Fin n → S → X)
    (outputs : Fin n → Y) :
    (blockChannel state channels n).transition (Policy.ofStrategies strategies) outputs =
      ((strategyChannel state channels).block n).transition strategies outputs := by
  simpa only [blockChannel_transition, Policy.input_ofStrategies,
    FiniteChannel.block_transition, strategyChannel_transition, FiniteProductProbability.mass]
    using FiniteProductProbability.sum_mass_mul_prod state
      (fun i s ↦ (channels s).transition (strategies i s) (outputs i))

/-- A deterministic causal code with a positive finite message set and output-only decoder. -/
@[capacity_shared_api]
structure BlockCode (state : FiniteDistribution S) (channels : S → FiniteChannel X Y)
    (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  encode : Fin messageCount → Policy S X blocklength
  decode : (Fin blocklength → Y) → Fin messageCount

namespace BlockCode

variable {state : FiniteDistribution S} {channels : S → FiniteChannel X Y}
variable {blocklength : ℕ}

/-- A causal code is a one-shot code for the induced policy channel. -/
@[capacity_shared_api]
def toOneShotCode (code : BlockCode state channels blocklength) :
    OneShotCode (blockChannel state channels blocklength) (Fin code.messageCount) where
  encode := code.encode
  decode := code.decode

/-- Average error includes the uniform message, iid states, and channel noise. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability (code : BlockCode state channels blocklength) : ℝ :=
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  code.toOneShotCode.averageErrorProbability

/-- Code rate in bits per physical channel use. -/
@[capacity_shared_api]
noncomputable def rate (code : BlockCode state channels blocklength) : ℝ :=
  Real.logb 2 code.messageCount / blocklength

/-- Implement an ordinary strategy-channel code by evaluating each strategy on the current state. -/
@[capacity_shared_api]
def ofStrategyCode
    (code : FiniteChannel.BlockCode (strategyChannel state channels) blocklength) :
    BlockCode state channels blocklength where
  messageCount := code.messageCount
  messageCount_pos := code.messageCount_pos
  encode message := Policy.ofStrategies (code.encode message)
  decode := code.decode

@[simp, capacity_shared_api]
theorem ofStrategyCode_messageCount
    (code : FiniteChannel.BlockCode (strategyChannel state channels) blocklength) :
    (ofStrategyCode code).messageCount = code.messageCount :=
  rfl

@[simp, capacity_shared_api]
theorem ofStrategyCode_rate
    (code : FiniteChannel.BlockCode (strategyChannel state channels) blocklength) :
    (ofStrategyCode code).rate = code.rate :=
  rfl

@[simp, capacity_shared_api]
theorem ofStrategyCode_averageErrorProbability
    (code : FiniteChannel.BlockCode (strategyChannel state channels) blocklength) :
    (ofStrategyCode code).averageErrorProbability = code.averageErrorProbability := by
  simp only [averageErrorProbability, FiniteChannel.BlockCode.averageErrorProbability,
    OneShotCode.averageErrorProbability, OneShotCode.averageSuccessProbability,
    OneShotCode.successProbability, toOneShotCode, FiniteChannel.BlockCode.toOneShotCode,
    ofStrategyCode, blockChannel_transition_ofStrategies]
  rfl

end BlockCode

/-- Causal coding at every sufficiently large blocklength, with vanishing average error. -/
@[capacity_shared_api]
def AchievableRate (state : FiniteDistribution S) (channels : S → FiniteChannel X Y)
    (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ firstBlocklength : ℕ, 0 < firstBlocklength ∧
    ∀ blocklength, firstBlocklength ≤ blocklength →
      ∃ code : BlockCode state channels blocklength,
        code.averageErrorProbability ≤ ε ∧ rate ≤ code.rate

/-- Operational capacity of deterministic causal codes, in bits per physical channel use. -/
@[capacity_shared_api]
noncomputable def operationalCapacityBits (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) : ℝ :=
  sSup {rate | AchievableRate state channels rate}

/-- Every rate achievable on the strategy channel is achievable with causal state knowledge. -/
@[capacity_shared_api]
theorem achievableRate_of_strategyChannel {state : FiniteDistribution S}
    {channels : S → FiniteChannel X Y} {rate : ℝ}
    (hrate : (strategyChannel state channels).AchievableRate rate) :
    AchievableRate state channels rate := by
  intro ε hε
  obtain ⟨first, hfirst, hcodes⟩ := hrate ε hε
  refine ⟨first, hfirst, ?_⟩
  intro n hn
  obtain ⟨code, herror, hcodeRate⟩ := hcodes n hn
  exact ⟨BlockCode.ofStrategyCode code, by simpa using herror, by simpa using hcodeRate⟩

end CapacityAtlas.CausalState
