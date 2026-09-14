/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteBroadcastChannel
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import Mathlib.Analysis.Convex.Hull

open scoped BigOperators

namespace CapacityAtlas.PrivateMessageBroadcast

variable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-- Independent private messages, a joint encoder, and a decoder at each receiver. -/
structure Code (W : FiniteBroadcastChannel X Y₁ Y₂) (n : ℕ) where
  messages₁ : ℕ
  messages₂ : ℕ
  messages₁_pos : 0 < messages₁
  messages₂_pos : 0 < messages₂
  encode : Fin messages₁ → Fin messages₂ → Fin n → X
  decode₁ : (Fin n → Y₁) → Fin messages₁
  decode₂ : (Fin n → Y₂) → Fin messages₂

/-- Maximum of the two average block-error probabilities. Vanishing error is
independent of the coupling chosen for the two receiver marginals. -/
noncomputable def error {W : FiniteBroadcastChannel X Y₁ Y₂} {n : ℕ}
    (c : Code W n) : ℝ := by
  classical
  let e₁ := (c.messages₁ * c.messages₂ : ℝ)⁻¹ *
    ∑ m₁, ∑ m₂, ∑ y : Fin n → Y₁,
      if c.decode₁ y = m₁ then 0 else (W.receiver₁.block n).transition (c.encode m₁ m₂) y
  let e₂ := (c.messages₁ * c.messages₂ : ℝ)⁻¹ *
    ∑ m₁, ∑ m₂, ∑ y : Fin n → Y₂,
      if c.decode₂ y = m₂ then 0 else (W.receiver₂.block n).transition (c.encode m₁ m₂) y
  exact max e₁ e₂

/-- Error that at least one receiver fails, under an explicit joint physical law.
Use only with the marginal equalities stated in `broadcastErrorConventionBridge`. -/
noncomputable def jointError {W : FiniteBroadcastChannel X Y₁ Y₂} {n : ℕ}
    (V : FiniteChannel X (Y₁ × Y₂)) (c : Code W n) : ℝ := by
  classical
  exact (c.messages₁ * c.messages₂ : ℝ)⁻¹ *
    ∑ m₁, ∑ m₂, ∑ ys : Fin n → Y₁ × Y₂,
      if c.decode₁ (fun t ↦ (ys t).1) = m₁ ∧ c.decode₂ (fun t ↦ (ys t).2) = m₂
      then 0 else (V.block n).transition (c.encode m₁ m₂) ys

noncomputable def rates {W : FiniteBroadcastChannel X Y₁ Y₂} {n : ℕ}
    (c : Code W n) : RatePair :=
  (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n)

/-- Operational private-message capacity region, not a single-letter expression. -/
noncomputable def capacityRegion (W : FiniteBroadcastChannel X Y₁ Y₂) : Set RatePair :=
  Operational.achievableRegion (Code W) (fun _ _ ↦ True)
    (fun _ c ↦ error c) (fun _ c ↦ rates c)

/-- Stochastic degradation of receiver 2 from receiver 1. Marginals suffice here
because there is no receiver feedback. -/
def IsDegraded (W : FiniteBroadcastChannel X Y₁ Y₂) : Prop :=
  ∃ degrade : FiniteChannel Y₁ Y₂, W.receiver₂ = degrade.comp W.receiver₁

/-- Joint law of auxiliaries, input, and one output. -/
def auxiliaryJoint {u v : ℕ} (p : FiniteDistribution (Fin u × Fin v × X))
    {Y : Type*} [Fintype Y] (W : FiniteChannel X Y) :=
  FiniteInformation.joint p (W.encoded fun a ↦ a.2.2)

/-- The original two-auxiliary Marton inner region, with explicit convexification.
This is a fixed published version, not an unspecified best-known inner bound. -/
noncomputable def martonRegion (W : FiniteBroadcastChannel X Y₁ Y₂) : Set RatePair :=
  closure (convexHull ℝ {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ u v : ℕ, ∃ p : FiniteDistribution (Fin u × Fin v × X),
      let p₁ := auxiliaryJoint p W.receiver₁
      let p₂ := auxiliaryJoint p W.receiver₂
      let a := FiniteInformation.information p₁ (fun z ↦ z.1.1) Prod.snd
      let b := FiniteInformation.information p₂ (fun z ↦ z.1.2.1) Prod.snd
      r.1 ≤ a ∧ r.2 ≤ b ∧ r.1 + r.2 ≤ a + b -
        FiniteInformation.information p Prod.fst (fun z ↦ z.2.1)})

/-- UV outer region for private messages. All four inequalities use the same
joint auxiliary/input law. No arbitrary region is passed as a hypothesis. -/
noncomputable def uvRegion (W : FiniteBroadcastChannel X Y₁ Y₂) : Set RatePair :=
  closure {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ u v : ℕ, ∃ p : FiniteDistribution (Fin u × Fin v × X),
      let p₁ := auxiliaryJoint p W.receiver₁
      let p₂ := auxiliaryJoint p W.receiver₂
      let a := FiniteInformation.information p₁ (fun z ↦ z.1.1) Prod.snd
      let b := FiniteInformation.information p₂ (fun z ↦ z.1.2.1) Prod.snd
      r.1 ≤ a ∧ r.2 ≤ b ∧
      r.1 + r.2 ≤ a + FiniteInformation.conditional p₂
        (fun z ↦ z.1.2.2) Prod.snd (fun z ↦ z.1.1) ∧
      r.1 + r.2 ≤ b + FiniteInformation.conditional p₁
        (fun z ↦ z.1.2.2) Prod.snd (fun z ↦ z.1.2.1)}

end CapacityAtlas.PrivateMessageBroadcast
