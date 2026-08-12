/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import CapacityAtlasForMathlib.Network.IndexCoding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic

open scoped BigOperators

namespace CapacityAtlas.ReportedTargets

abbrev RatePair := ℝ × ℝ

/-- An operational scalar-capacity interface, separated from a channel's physical model. -/
@[capacity_shared_api]
structure ScalarOperationalTheory (Model : Type*) where
  achievable : Model → ℝ → Prop

namespace ScalarOperationalTheory

@[capacity_shared_api]
noncomputable def capacity {Model : Type*} (theory : ScalarOperationalTheory Model)
    (model : Model) : ℝ :=
  sSup {rate | theory.achievable model rate}

end ScalarOperationalTheory

/-- An operational two-rate capacity-region interface. -/
@[capacity_shared_api]
structure RegionOperationalTheory (Model : Type*) where
  achievable : Model → RatePair → Prop

namespace RegionOperationalTheory

@[capacity_shared_api]
def capacityRegion {Model : Type*} (theory : RegionOperationalTheory Model)
    (model : Model) : Set RatePair :=
  {rate | theory.achievable model rate}

end RegionOperationalTheory

/-- A deterministic finite channel induced by a map of alphabets. -/
@[capacity_shared_api]
def deterministicFiniteChannel (X Y : Type*) [Fintype X] [Fintype Y]
    [DecidableEq Y] (output : X → Y) : FiniteChannel X Y where
  transition input received := if received = output input then 1 else 0
  nonnegative input received := by split <;> positivity
  row_sum input := by simp

/-! ## General finite wiretap channel -/

/-- Two finite DMCs with a common input, one legitimate and one eavesdropping. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure FiniteWiretapChannel (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z] where
  legitimate : FiniteChannel X Y
  eavesdropper : FiniteChannel X Z

/-- A stochastic wiretap block code; `randomizationCount` is private encoder randomness. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure WiretapCode {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (channel : FiniteWiretapChannel X Y Z) (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  randomizationCount : ℕ
  randomizationCount_pos : 0 < randomizationCount
  encode : Fin messageCount → Fin randomizationCount → Fin blocklength → X
  decode : (Fin blocklength → Y) → Fin messageCount

/-- Strong and weak secrecy are deliberately different operational predicates. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure WiretapOperationalTheory (Model : Type*) where
  strongSecrecyAchievable : Model → ℝ → Prop
  weakSecrecyAchievable : Model → ℝ → Prop

namespace WiretapOperationalTheory

noncomputable def strongCapacity {Model : Type*} (theory : WiretapOperationalTheory Model)
    (model : Model) : ℝ :=
  sSup {rate | theory.strongSecrecyAchievable model rate}

noncomputable def weakCapacity {Model : Type*} (theory : WiretapOperationalTheory Model)
    (model : Model) : ℝ :=
  sSup {rate | theory.weakSecrecyAchievable model rate}

end WiretapOperationalTheory

/-- A finite auxiliary `V`, its law, and a stochastic prefixing channel `V → X`. -/
structure WiretapAuxiliary (X : Type*) [Fintype X] where
  Carrier : Type
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier
  distribution : @FiniteDistribution Carrier fintype
  encoder : @FiniteChannel Carrier X fintype inferInstance

noncomputable def wiretapAuxiliaryInformation {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (channel : FiniteWiretapChannel X Y Z) (auxiliary : WiretapAuxiliary X) : ℝ := by
  letI := auxiliary.fintype
  letI := auxiliary.decidableEq
  exact (channel.legitimate.comp auxiliary.encoder).mutualInformationBits
      auxiliary.distribution -
    (channel.eavesdropper.comp auxiliary.encoder).mutualInformationBits
      auxiliary.distribution

/-- The standard single-auxiliary value for an unconstrained finite wiretap channel. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
noncomputable def finiteWiretapAuxiliaryCapacity {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (channel : FiniteWiretapChannel X Y Z) : ℝ :=
  sSup (Set.range (wiretapAuxiliaryInformation channel))

/-- Strong-secrecy capacity equals the single-auxiliary wiretap formula. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_statement]
def generalFiniteWiretapCapacityStatement {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (theory : WiretapOperationalTheory (FiniteWiretapChannel X Y Z))
    (channel : FiniteWiretapChannel X Y Z) : Prop :=
  theory.strongCapacity channel = finiteWiretapAuxiliaryCapacity channel

/-- Strong and weak secrecy have the same capacity, without identifying their criteria. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_statement]
def generalFiniteWiretapStrongWeakAgreement {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (theory : WiretapOperationalTheory (FiniteWiretapChannel X Y Z))
    (channel : FiniteWiretapChannel X Y Z) : Prop :=
  theory.strongCapacity channel = theory.weakCapacity channel

/-! ## Finite broadcast channels -/

/-- A two-receiver broadcast channel is determined by its two marginal DMCs. -/
@[capacity_shared_api]
structure FiniteBroadcastChannel (X Y₁ Y₂ : Type*)
    [Fintype X] [Fintype Y₁] [Fintype Y₂] where
  receiver₁ : FiniteChannel X Y₁
  receiver₂ : FiniteChannel X Y₂

/-- A finite superposition auxiliary distribution and stochastic encoder. -/
structure BroadcastAuxiliary (X : Type*) [Fintype X] where
  Carrier : Type
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier
  distribution : @FiniteDistribution Carrier fintype
  encoder : @FiniteChannel Carrier X fintype inferInstance

noncomputable def BroadcastAuxiliary.weakInformation {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteBroadcastChannel X Y₁ Y₂) (auxiliary : BroadcastAuxiliary X) : ℝ := by
  letI := auxiliary.fintype
  letI := auxiliary.decidableEq
  exact (channel.receiver₂.comp auxiliary.encoder).mutualInformationBits
    auxiliary.distribution

noncomputable def BroadcastAuxiliary.strongConditionalInformation {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteBroadcastChannel X Y₁ Y₂) (auxiliary : BroadcastAuxiliary X) : ℝ := by
  letI := auxiliary.fintype
  letI := auxiliary.decidableEq
  exact ∑ value, auxiliary.distribution value *
    channel.receiver₁.mutualInformationBits (auxiliary.encoder.rowDistribution value)

/-- The superposition region with receiver 1 as the ordered stronger receiver. -/
@[capacity_shared_api]
noncomputable def superpositionRegion {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteBroadcastChannel X Y₁ Y₂) : Set RatePair :=
  {rate | 0 ≤ rate.1 ∧ 0 ≤ rate.2 ∧ ∃ auxiliary : BroadcastAuxiliary X,
    rate.1 ≤ auxiliary.strongConditionalInformation channel ∧
      rate.2 ≤ auxiliary.weakInformation channel}

/-- The private-message region for a more-capable receiver ordering. -/
@[capacity_shared_api]
noncomputable def moreCapableRegion {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteBroadcastChannel X Y₁ Y₂) : Set RatePair :=
  {rate | 0 ≤ rate.1 ∧ 0 ≤ rate.2 ∧ ∃ auxiliary : BroadcastAuxiliary X,
    rate.2 ≤ auxiliary.weakInformation channel ∧
      rate.1 + rate.2 ≤ min
        (channel.receiver₁.mutualInformationBits
          (by
            letI := auxiliary.fintype
            letI := auxiliary.decidableEq
            exact auxiliary.encoder.outputDistribution auxiliary.distribution))
        (auxiliary.strongConditionalInformation channel +
          auxiliary.weakInformation channel)}

/-- Receiver 1 is more capable when it has at least as much mutual information for every input law. -/
@[capacity_problem "more-capable-broadcast-channel", capacity_definition]
def FiniteBroadcastChannel.IsMoreCapable {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteBroadcastChannel X Y₁ Y₂) : Prop :=
  ∀ input : FiniteDistribution X,
    channel.receiver₂.mutualInformationBits input ≤
      channel.receiver₁.mutualInformationBits input

/-- Receiver 1 is less noisy when it dominates after every finite stochastic prefix. -/
@[capacity_problem "less-noisy-broadcast-channel", capacity_definition]
def FiniteBroadcastChannel.IsLessNoisy {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteBroadcastChannel X Y₁ Y₂) : Prop :=
  ∀ auxiliary : BroadcastAuxiliary X,
    auxiliary.weakInformation channel ≤
      (by
        letI := auxiliary.fintype
        letI := auxiliary.decidableEq
        exact (channel.receiver₁.comp auxiliary.encoder).mutualInformationBits
          auxiliary.distribution)

@[capacity_problem "less-noisy-broadcast-channel", capacity_statement]
def lessNoisyBroadcastCapacityStatement {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (theory : RegionOperationalTheory (FiniteBroadcastChannel X Y₁ Y₂))
    (channel : FiniteBroadcastChannel X Y₁ Y₂) : Prop :=
  channel.IsLessNoisy → theory.capacityRegion channel = superpositionRegion channel

@[capacity_problem "more-capable-broadcast-channel", capacity_statement]
def moreCapableBroadcastCapacityStatement {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (theory : RegionOperationalTheory (FiniteBroadcastChannel X Y₁ Y₂))
    (channel : FiniteBroadcastChannel X Y₁ Y₂) : Prop :=
  channel.IsMoreCapable → theory.capacityRegion channel = moreCapableRegion channel

def blackwellOutput₁ : Fin 3 → Bool := ![false, false, true]
def blackwellOutput₂ : Fin 3 → Bool := ![false, true, true]

/-- The three-input deterministic Blackwell broadcast channel. -/
@[capacity_problem "blackwell-broadcast-channel", capacity_definition]
def blackwellBroadcastChannel : FiniteBroadcastChannel (Fin 3) Bool Bool where
  receiver₁ := deterministicFiniteChannel (Fin 3) Bool blackwellOutput₁
  receiver₂ := deterministicFiniteChannel (Fin 3) Bool blackwellOutput₂

/-- The deterministic Blackwell single-letter private-message region. -/
@[capacity_problem "blackwell-broadcast-channel", capacity_definition]
noncomputable def blackwellCapacityRegion : Set RatePair :=
  {rate | 0 ≤ rate.1 ∧ 0 ≤ rate.2 ∧ ∃ input : FiniteDistribution (Fin 3),
    rate.1 ≤ (input.map blackwellOutput₁).entropyBits ∧
      rate.2 ≤ (input.map blackwellOutput₂).entropyBits ∧
      rate.1 + rate.2 ≤ input.entropyBits}

@[capacity_problem "blackwell-broadcast-channel", capacity_statement]
def blackwellBroadcastCapacityStatement
    (theory : RegionOperationalTheory (FiniteBroadcastChannel (Fin 3) Bool Bool)) : Prop :=
  theory.capacityRegion blackwellBroadcastChannel = blackwellCapacityRegion

/-- The binary skew-symmetric channel's opposite deterministic/noisy branches. -/
@[capacity_problem "binary-skew-symmetric-broadcast-channel", capacity_definition]
noncomputable def binarySkewSymmetricBroadcastChannel :
    FiniteBroadcastChannel Bool Bool Bool where
  receiver₁ := {
    transition input output :=
      if input = false then if output = false then 1 else 0 else 1 / 2
    nonnegative input output := by
      by_cases hinput : input = false <;>
        by_cases houtput : output = false <;> simp [hinput, houtput]
    row_sum input := by cases input <;> norm_num [Fintype.sum_bool] }
  receiver₂ := {
    transition input output :=
      if input = true then if output = true then 1 else 0 else 1 / 2
    nonnegative input output := by
      by_cases hinput : input = true <;>
        by_cases houtput : output = true <;> simp [hinput, houtput]
    row_sum input := by cases input <;> norm_num [Fintype.sum_bool] }

/-- The flagship BSSC question: does Marton's inner region meet the UV outer region? -/
@[capacity_problem "binary-skew-symmetric-broadcast-channel", capacity_statement]
def binarySkewSymmetricBroadcastCapacityStatement
    (martonInnerRegion uvOuterRegion :
      FiniteBroadcastChannel Bool Bool Bool → Set RatePair) : Prop :=
  martonInnerRegion binarySkewSymmetricBroadcastChannel =
    uvOuterRegion binarySkewSymmetricBroadcastChannel

/-! ## Strong interference -/

/-- A two-user DMC specified by the two receiver marginals. -/
@[capacity_problem "strong-interference-two-user-dmc", capacity_definition]
structure FiniteInterferenceChannel (X₁ X₂ Y₁ Y₂ : Type*)
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂] where
  receiver₁ : FiniteChannel (X₁ × X₂) Y₁
  receiver₂ : FiniteChannel (X₁ × X₂) Y₂

def FiniteInterferenceChannel.user₁ToReceiver₁ {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) (input₂ : X₂) :
    FiniteChannel X₁ Y₁ where
  transition input₁ := channel.receiver₁.transition (input₁, input₂)
  nonnegative input₁ := channel.receiver₁.nonnegative (input₁, input₂)
  row_sum input₁ := channel.receiver₁.row_sum (input₁, input₂)

def FiniteInterferenceChannel.user₁ToReceiver₂ {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) (input₂ : X₂) :
    FiniteChannel X₁ Y₂ where
  transition input₁ := channel.receiver₂.transition (input₁, input₂)
  nonnegative input₁ := channel.receiver₂.nonnegative (input₁, input₂)
  row_sum input₁ := channel.receiver₂.row_sum (input₁, input₂)

def FiniteInterferenceChannel.user₂ToReceiver₁ {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) (input₁ : X₁) :
    FiniteChannel X₂ Y₁ where
  transition input₂ := channel.receiver₁.transition (input₁, input₂)
  nonnegative input₂ := channel.receiver₁.nonnegative (input₁, input₂)
  row_sum input₂ := channel.receiver₁.row_sum (input₁, input₂)

def FiniteInterferenceChannel.user₂ToReceiver₂ {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) (input₁ : X₁) :
    FiniteChannel X₂ Y₂ where
  transition input₂ := channel.receiver₂.transition (input₁, input₂)
  nonnegative input₂ := channel.receiver₂.nonnegative (input₁, input₂)
  row_sum input₂ := channel.receiver₂.row_sum (input₁, input₂)

/-- The two standard strong-interference inequalities, for every product input law. -/
@[capacity_problem "strong-interference-two-user-dmc", capacity_definition]
def FiniteInterferenceChannel.IsStrongInterference {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) : Prop :=
  ∀ input₁ : FiniteDistribution X₁, ∀ input₂ : FiniteDistribution X₂,
    (∑ x₂, input₂ x₂ *
      (channel.user₁ToReceiver₁ x₂).mutualInformationBits input₁) ≤
      ∑ x₂, input₂ x₂ *
        (channel.user₁ToReceiver₂ x₂).mutualInformationBits input₁ ∧
    (∑ x₁, input₁ x₁ *
      (channel.user₂ToReceiver₂ x₁).mutualInformationBits input₂) ≤
      ∑ x₁, input₁ x₁ *
        (channel.user₂ToReceiver₁ x₁).mutualInformationBits input₂

@[capacity_problem "strong-interference-two-user-dmc", capacity_statement]
def strongInterferenceCapacityStatement {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (theory : RegionOperationalTheory (FiniteInterferenceChannel X₁ X₂ Y₁ Y₂))
    (macIntersectionRegion : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂ → Set RatePair)
    (channel : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) : Prop :=
  channel.IsStrongInterference →
    theory.capacityRegion channel = macIntersectionRegion channel

/-! ## Primitive relay channel -/

/-- A relay observation and destination output followed by an orthogonal noiseless bit-pipe. -/
@[capacity_problem "primitive-relay-channel", capacity_definition]
structure PrimitiveRelayChannel (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z] where
  broadcast : FiniteChannel X (Y × Z)
  relayLinkCapacityBits : ℝ
  relayLinkCapacity_nonnegative : 0 ≤ relayLinkCapacityBits

@[capacity_problem "primitive-relay-channel", capacity_statement]
def primitiveRelayCapacityBoundsStatement {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (theory : ScalarOperationalTheory (PrimitiveRelayChannel X Y Z))
    (compressForwardBound improvedUpperBound cutSetBound :
      PrimitiveRelayChannel X Y Z → ℝ)
    (channel : PrimitiveRelayChannel X Y Z) : Prop :=
  compressForwardBound channel ≤ theory.capacity channel ∧
    theory.capacity channel ≤ improvedUpperBound channel ∧
      improvedUpperBound channel ≤ cutSetBound channel

/-! ## Seven-cycle zero-error capacity -/

def sevenCycleAdjacent (left right : Fin 7) : Prop :=
  left.val = (right.val + 1) % 7 ∨ right.val = (left.val + 1) % 7

instance : DecidableRel sevenCycleAdjacent := fun left right ↦ by
  unfold sevenCycleAdjacent
  infer_instance

def IsGraphZeroErrorCode {Vertex : Type*} [DecidableEq Vertex]
    (adjacent : Vertex → Vertex → Prop) [DecidableRel adjacent]
    (blocklength : ℕ) (code : Finset (Fin blocklength → Vertex)) : Prop :=
  ∀ left ∈ code, ∀ right ∈ code, left ≠ right →
    ∃ coordinate, left coordinate ≠ right coordinate ∧
      ¬adjacent (left coordinate) (right coordinate)

noncomputable def graphShannonCapacity {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (adjacent : Vertex → Vertex → Prop) [DecidableRel adjacent] : ℝ :=
  sSup {rate | ∃ blocklength : ℕ, ∃ code : Finset (Fin blocklength → Vertex),
    0 < blocklength ∧ IsGraphZeroErrorCode adjacent blocklength code ∧
      rate = Real.rpow code.card ((blocklength : ℝ)⁻¹)}

@[capacity_problem "seven-cycle-zero-error-channel", capacity_definition]
noncomputable def sevenCycleShannonCapacity : ℝ :=
  graphShannonCapacity sevenCycleAdjacent

/-- The sourced finite-power lower certificate and Lovasz-theta upper bound. -/
@[capacity_problem "seven-cycle-zero-error-channel", capacity_statement]
def sevenCycleKnownBounds : Prop :=
  Real.rpow 367 ((5 : ℝ)⁻¹) ≤ sevenCycleShannonCapacity ∧
    sevenCycleShannonCapacity ≤
      7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7))

/-! ## Trapdoor and insertion channels -/

/-- A finite-state one-step channel, including its next-state transition. -/
@[capacity_shared_api]
structure FiniteStateChannel (X State Y : Type*)
    [Fintype X] [Fintype State] [Fintype Y] where
  transition : X → State → Y → State → ℝ
  nonnegative : ∀ input state output nextState,
    0 ≤ transition input state output nextState
  row_sum : ∀ input state, ∑ output, ∑ nextState,
    transition input state output nextState = 1

noncomputable def trapdoorTransition : Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => 1
  | true, true, true, true => 1
  | false, true, false, true => 1 / 2
  | false, true, true, false => 1 / 2
  | true, false, true, false => 1 / 2
  | true, false, false, true => 1 / 2
  | _, _, _, _ => 0

/-- The binary trapdoor channel: one of the stored and inserted bits leaves uniformly. -/
noncomputable def trapdoorChannel : FiniteStateChannel Bool Bool Bool where
  transition := trapdoorTransition
  nonnegative input state output nextState := by
    cases input <;> cases state <;> cases output <;> cases nextState <;>
      norm_num [trapdoorTransition]
  row_sum input state := by
    cases input <;> cases state <;> norm_num [trapdoorTransition, Fintype.sum_bool]

@[capacity_problem "trapdoor-channel-with-feedback", capacity_definition]
noncomputable def trapdoorFeedbackModel : FiniteStateChannel Bool Bool Bool :=
  trapdoorChannel

@[capacity_problem "trapdoor-channel-without-feedback", capacity_definition]
noncomputable def trapdoorFeedforwardModel : FiniteStateChannel Bool Bool Bool :=
  trapdoorChannel

/-- Feedback permits causal dependence on past outputs; the initial state is fixed and known. -/
@[capacity_problem "trapdoor-channel-with-feedback", capacity_statement]
def trapdoorFeedbackCapacityStatement
  (feedbackTheory : ScalarOperationalTheory (FiniteStateChannel Bool Bool Bool)) : Prop :=
  feedbackTheory.capacity trapdoorFeedbackModel =
    Real.log ((1 + Real.sqrt 5) / 2) / Real.log 2

/-- Feedforward capacity remains distinct from the solved feedback quantity. -/
@[capacity_problem "trapdoor-channel-without-feedback", capacity_statement]
def trapdoorWithoutFeedbackCapacityBounds
  (feedforwardTheory : ScalarOperationalTheory (FiniteStateChannel Bool Bool Bool)) : Prop :=
  0 ≤ feedforwardTheory.capacity trapdoorFeedforwardModel ∧
    feedforwardTheory.capacity trapdoorFeedforwardModel ≤ 1

/-- A finite-support variable-length one-step channel. -/
structure VariableLengthChannelStep (X Y : Type*) [Fintype X] [Fintype Y]
    [DecidableEq Y] where
  support : X → Finset (List Y)
  transition : X → List Y → ℝ
  nonnegative : ∀ input output, 0 ≤ transition input output
  row_sum : ∀ input, ∑ output ∈ support input, transition input output = 1
  zero_outside : ∀ input output, output ∉ support input → transition input output = 0

/-- After each transmitted bit, independently insert one fair bit with probability `p`. -/
@[capacity_problem "binary-insertion-channel", capacity_definition]
noncomputable def randomBinaryInsertionStep (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    VariableLengthChannelStep Bool Bool where
  support input := {[input], [input, false], [input, true]}
  transition input output :=
    if output = [input] then 1 - p
    else if output = [input, false] ∨ output = [input, true] then p / 2
    else 0
  nonnegative input output := by
    split
    · linarith
    · split <;> positivity
  row_sum input := by
    cases input <;> simp
  zero_outside input output hout := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
    rcases hout with ⟨hword, hfalse, htrue⟩
    simp [hword, hfalse, htrue]

@[capacity_problem "binary-insertion-channel", capacity_statement]
def binaryInsertionCapacityBounds (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (theory : ScalarOperationalTheory (VariableLengthChannelStep Bool Bool)) : Prop :=
  0 ≤ theory.capacity (randomBinaryInsertionStep p hp0 hp1) ∧
    theory.capacity (randomBinaryInsertionStep p hp0 hp1) ≤ 1

/-! ## Point-to-point Gaussian MIMO -/

/-- A real Gaussian MIMO channel with total input power and white-noise variance. -/
@[capacity_problem "gaussian-mimo-channel", capacity_definition]
structure RealGaussianMIMOModel (transmitAntennas receiveAntennas : ℕ) where
  channelMatrix : Matrix (Fin receiveAntennas) (Fin transmitAntennas) ℝ
  noiseVariance : ℝ
  noiseVariance_pos : 0 < noiseVariance
  totalPower : ℝ
  totalPower_nonnegative : 0 ≤ totalPower

/-- Real-channel normalization uses `1/2 log₂ det`; the value argument is the water-filling optimum. -/
@[capacity_problem "gaussian-mimo-channel", capacity_statement]
def gaussianMIMOCapacityStatement (transmitAntennas receiveAntennas : ℕ)
    (theory : ScalarOperationalTheory
      (RealGaussianMIMOModel transmitAntennas receiveAntennas))
    (waterFillingLogDetValue :
      RealGaussianMIMOModel transmitAntennas receiveAntennas → ℝ)
    (channel : RealGaussianMIMOModel transmitAntennas receiveAntennas) : Prop :=
  theory.capacity channel = waterFillingLogDetValue channel

/-! ## Small index-coding benchmark -/

/-- The published composite-coding formula covers every rate vector through five messages. -/
@[capacity_problem "index-coding-at-most-five-messages", capacity_statement]
def indexCodingAtMostFiveMessagesCapacityRegions
    (operationalRegion compositeCodingRegion :
      ∀ messageCount : ℕ,
        IndexCoding.Instance (Fin messageCount) (Fin messageCount) →
          Set (Fin messageCount → ℝ)) : Prop :=
  ∀ messageCount : ℕ, 0 < messageCount → messageCount ≤ 5 →
    ∀ problem : IndexCoding.Instance (Fin messageCount) (Fin messageCount),
      operationalRegion messageCount problem = compositeCodingRegion messageCount problem

/-- Shannon-polymatroid bounds are tight for every multiple-unicast instance up to five messages. -/
@[capacity_problem "index-coding-at-most-five-messages", capacity_statement]
def indexCodingAtMostFiveMessagesStatement : Prop :=
  ∀ messageCount : ℕ, 0 < messageCount → messageCount ≤ 5 →
    ∀ problem : IndexCoding.Instance (Fin messageCount) (Fin messageCount),
      IndexCoding.symmetricCapacity problem =
        IndexCoding.shannonPolymatroidOuterBound problem

end CapacityAtlas.ReportedTargets
