/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian

structure MACCode (n : ℕ) where
  messages₁ : ℕ
  messages₂ : ℕ
  messages₁_pos : 0 < messages₁
  messages₂_pos : 0 < messages₂
  encode₁ : Fin messages₁ → Fin n → ℝ
  encode₂ : Fin messages₂ → Fin n → ℝ
  decode₁ : Decoder (Fin n → ℝ) messages₁
  decode₂ : Decoder (Fin n → ℝ) messages₂

def SeparateCodewordPowerAdmissible (P₁ P₂ : ℝ) {n : ℕ} (c : MACCode n) : Prop :=
  (∀ m, (∑ t, (c.encode₁ m t) ^ 2) ≤ (n : ℝ) * P₁) ∧
    ∀ m, (∑ t, (c.encode₂ m t) ^ 2) ≤ (n : ℝ) * P₂

noncomputable def macError (N : ℝ) {n : ℕ} (c : MACCode n) : ℝ :=
  (c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂,
    ((noise N n) {z |
      let y := fun t ↦ c.encode₁ m₁ t + c.encode₂ m₂ t + z t
      ¬(c.decode₁.apply y = m₁ ∧ c.decode₂.apply y = m₂)}).toReal

noncomputable def macCapacityRegion (P₁ P₂ N : ℝ) : Set RatePair :=
  Operational.achievableRegion MACCode (fun _ c ↦ SeparateCodewordPowerAdmissible P₁ P₂ c)
    (fun _ c ↦ macError N c)
    (fun n c ↦ (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n))

noncomputable def macRegion (P₁ P₂ N : ℝ) : Set RatePair :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 ≤ awgnFormula P₁ N ∧
    r.2 ≤ awgnFormula P₂ N ∧ r.1 + r.2 ≤ awgnFormula (P₁ + P₂) N}

structure BroadcastCode (n : ℕ) where
  messages₁ : ℕ
  messages₂ : ℕ
  messages₁_pos : 0 < messages₁
  messages₂_pos : 0 < messages₂
  encode : Fin messages₁ → Fin messages₂ → Fin n → ℝ
  decode₁ : Decoder (Fin n → ℝ) messages₁
  decode₂ : Decoder (Fin n → ℝ) messages₂

def MessagePairPowerAdmissible (P : ℝ) {n : ℕ} (c : BroadcastCode n) : Prop :=
  ∀ m₁ m₂, (∑ t, (c.encode m₁ m₂ t) ^ 2) ≤ (n : ℝ) * P

/-- Nonfeedback broadcast reliability depends only on receiver marginals. -/
noncomputable def broadcastError (N₁ N₂ : ℝ) {n : ℕ} (c : BroadcastCode n) : ℝ :=
  max
    ((c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂,
      ((noise N₁ n) {z | c.decode₁.apply (fun t ↦ c.encode m₁ m₂ t + z t) ≠ m₁}).toReal)
    ((c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂,
      ((noise N₂ n) {z | c.decode₂.apply (fun t ↦ c.encode m₁ m₂ t + z t) ≠ m₂}).toReal)

noncomputable def broadcastCapacityRegion (P N₁ N₂ : ℝ) : Set RatePair :=
  Operational.achievableRegion BroadcastCode (fun _ c ↦ MessagePairPowerAdmissible P c)
    (fun _ c ↦ broadcastError N₁ N₂ c)
    (fun n c ↦ (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n))

noncomputable def broadcastRegion (P N₁ N₂ : ℝ) : Set RatePair :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
    r.1 ≤ awgnFormula (α * P) N₁ ∧
    r.2 ≤ awgnFormula ((1 - α) * P) (α * P + N₂)}

end CapacityAtlas.Gaussian
