/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteBroadcastChannel

namespace CapacityAtlas.Channel

open CapacityAtlas

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
  receiver₁ := FiniteChannel.deterministic blackwellOutput₁
  receiver₂ := FiniteChannel.deterministic blackwellOutput₂

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

end CapacityAtlas.Channel
