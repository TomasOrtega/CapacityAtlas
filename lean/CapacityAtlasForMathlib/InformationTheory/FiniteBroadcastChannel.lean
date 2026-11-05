/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.RateRegion

open scoped BigOperators

namespace CapacityAtlas

/-- A two-receiver broadcast channel is determined by its two marginal DMCs. -/
@[capacity_shared_api]
structure FiniteBroadcastChannel (X Y₁ Y₂ : Type*)
    [Fintype X] [Fintype Y₁] [Fintype Y₂] where
  /-- Marginal channel from the input to the first receiver. -/
  receiver₁ : FiniteChannel X Y₁
  /-- Marginal channel from the input to the second receiver. -/
  receiver₂ : FiniteChannel X Y₂

/-- A finite superposition auxiliary distribution and stochastic encoder. -/
structure BroadcastAuxiliary (X : Type*) [Fintype X] where
  /-- Type of auxiliary symbols. -/
  Carrier : Type
  /-- Finite enumeration of the auxiliary alphabet. -/
  fintype : Fintype Carrier
  /-- Decidable equality for auxiliary symbols. -/
  decidableEq : DecidableEq Carrier
  /-- Probability law of the auxiliary symbol. -/
  distribution : @FiniteDistribution Carrier fintype
  /-- Stochastic prefixing channel from the auxiliary alphabet to physical inputs. -/
  encoder : @FiniteChannel Carrier X fintype inferInstance

/-- Mutual information from the auxiliary to the second receiver, in bits. -/
noncomputable def BroadcastAuxiliary.weakInformation {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (channel : FiniteBroadcastChannel X Y₁ Y₂) (auxiliary : BroadcastAuxiliary X) : ℝ := by
  letI := auxiliary.fintype
  letI := auxiliary.decidableEq
  exact (channel.receiver₂.comp auxiliary.encoder).mutualInformationBits
    auxiliary.distribution

/-- First-receiver input-output mutual information averaged over the auxiliary, in bits. -/
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

end CapacityAtlas
