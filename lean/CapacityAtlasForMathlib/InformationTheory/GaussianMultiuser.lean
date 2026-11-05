/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian

/--
Two independently encoded finite messages with separate decoders observing the same real output
block.
-/
structure MACCode (n : ℕ) where
  /-- Number of messages for sender one. -/
  messages₁ : ℕ
  /-- Number of messages for sender two. -/
  messages₂ : ℕ
  /-- Sender one has a nonempty message alphabet. -/
  messages₁_pos : 0 < messages₁
  /-- Sender two has a nonempty message alphabet. -/
  messages₂_pos : 0 < messages₂
  /-- Sender-one codeword depending only on its own message. -/
  encode₁ : Fin messages₁ → Fin n → ℝ
  /-- Sender-two codeword depending only on its own message. -/
  encode₂ : Fin messages₂ → Fin n → ℝ
  /-- Measurable rule recovering sender one’s message from the common output. -/
  decode₁ : Decoder (Fin n → ℝ) messages₁
  /-- Measurable rule recovering sender two’s message from the common output. -/
  decode₂ : Decoder (Fin n → ℝ) messages₂

/-- Require every codeword of each sender to meet that sender’s block power budget. -/
def SeparateCodewordPowerAdmissible (P₁ P₂ : ℝ) {n : ℕ} (c : MACCode n) : Prop :=
  (∀ m, (∑ t, (c.encode₁ m t) ^ 2) ≤ (n : ℝ) * P₁) ∧
    ∀ m, (∑ t, (c.encode₂ m t) ^ 2) ≤ (n : ℝ) * P₂

/-- Average probability that either sender’s message is decoded incorrectly on the Gaussian MAC. -/
noncomputable def macError (N : ℝ) {n : ℕ} (c : MACCode n) : ℝ :=
  (c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂,
    ((noise N n) {z |
      let y := fun t ↦ c.encode₁ m₁ t + c.encode₂ m₂ t + z t
      ¬(c.decode₁.apply y = m₁ ∧ c.decode₂.apply y = m₂)}).toReal

/-- Closed achievable rate region of the Gaussian MAC with separate codeword power constraints. -/
noncomputable def macCapacityRegion (P₁ P₂ N : ℝ) : Set RatePair :=
  Operational.achievableRegion MACCode (fun _ c ↦ SeparateCodewordPowerAdmissible P₁ P₂ c)
    (fun _ c ↦ macError N c)
    (fun n c ↦ (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n))

/--
Nonnegative Gaussian MAC rate pairs satisfying the two individual and one sum-rate inequalities.
-/
noncomputable def macRegion (P₁ P₂ N : ℝ) : Set RatePair :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 ≤ awgnFormula P₁ N ∧
    r.2 ≤ awgnFormula P₂ N ∧ r.1 + r.2 ≤ awgnFormula (P₁ + P₂) N}

/-- Two-message real broadcast block code with one common encoder and receiver-specific decoders. -/
structure BroadcastCode (n : ℕ) where
  /-- Number of messages intended for receiver one. -/
  messages₁ : ℕ
  /-- Number of messages intended for receiver two. -/
  messages₂ : ℕ
  /-- Receiver one’s message alphabet is nonempty. -/
  messages₁_pos : 0 < messages₁
  /-- Receiver two’s message alphabet is nonempty. -/
  messages₂_pos : 0 < messages₂
  /-- Common transmitted block selected from both receivers’ messages. -/
  encode : Fin messages₁ → Fin messages₂ → Fin n → ℝ
  /-- Measurable decoder using only receiver one’s output block. -/
  decode₁ : Decoder (Fin n → ℝ) messages₁
  /-- Measurable decoder using only receiver two’s output block. -/
  decode₂ : Decoder (Fin n → ℝ) messages₂

/-- Require every encoded message pair to meet the transmitter’s block power budget. -/
def MessagePairPowerAdmissible (P : ℝ) {n : ℕ} (c : BroadcastCode n) : Prop :=
  ∀ m₁ m₂, (∑ t, (c.encode m₁ m₂ t) ^ 2) ≤ (n : ℝ) * P

/-- Nonfeedback broadcast reliability depends only on receiver marginals. -/
noncomputable def broadcastError (N₁ N₂ : ℝ) {n : ℕ} (c : BroadcastCode n) : ℝ :=
  max
    ((c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂,
      ((noise N₁ n) {z | c.decode₁.apply (fun t ↦ c.encode m₁ m₂ t + z t) ≠ m₁}).toReal)
    ((c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂,
      ((noise N₂ n) {z | c.decode₂.apply (fun t ↦ c.encode m₁ m₂ t + z t) ≠ m₂}).toReal)

/-- Closed achievable broadcast rate region under a power constraint for every message pair. -/
noncomputable def broadcastCapacityRegion (P N₁ N₂ : ℝ) : Set RatePair :=
  Operational.achievableRegion BroadcastCode (fun _ c ↦ MessagePairPowerAdmissible P c)
    (fun _ c ↦ broadcastError N₁ N₂ c)
    (fun n c ↦ (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n))

/-- Nonnegative rate pairs described by Gaussian superposition coding with power fraction `α`. -/
noncomputable def broadcastRegion (P N₁ N₂ : ℝ) : Set RatePair :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
    r.1 ≤ awgnFormula (α * P) N₁ ∧
    r.2 ≤ awgnFormula ((1 - α) * P) (α * P + N₂)}

end CapacityAtlas.Gaussian
