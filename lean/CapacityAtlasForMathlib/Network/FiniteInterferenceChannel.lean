/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

open scoped BigOperators

namespace CapacityAtlas

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

end CapacityAtlas
