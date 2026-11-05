/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.FiniteInterferenceChannel
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import Mathlib.Analysis.Convex.Hull

open scoped BigOperators

namespace CapacityAtlas.Interference

variable {X₁ X₂ Y₁ Y₂ : Type*}
variable [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]

/-- Independent messages and separate nonfeedback encoders. -/
structure Code (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) (n : ℕ) where
  /-- Number of messages available to the first sender. -/
  messages₁ : ℕ
  /-- Number of messages available to the second sender. -/
  messages₂ : ℕ
  /-- The first sender's message alphabet is nonempty. -/
  messages₁_pos : 0 < messages₁
  /-- The second sender's message alphabet is nonempty. -/
  messages₂_pos : 0 < messages₂
  /-- First sender's codeword determined solely by its own message. -/
  encode₁ : Fin messages₁ → Fin n → X₁
  /-- Second sender's codeword determined solely by its own message. -/
  encode₂ : Fin messages₂ → Fin n → X₂
  /-- First receiver's estimate of the first sender's message. -/
  decode₁ : (Fin n → Y₁) → Fin messages₁
  /-- Second receiver's estimate of the second sender's message. -/
  decode₂ : (Fin n → Y₂) → Fin messages₂

/-- Maximum of the two receiver error probabilities, averaged over independent uniform messages. -/
noncomputable def error {W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂} {n : ℕ}
    (c : Code W n) : ℝ := by
  classical
  let e₁ := (c.messages₁ * c.messages₂ : ℝ)⁻¹ *
    ∑ a, ∑ b, ∑ y : Fin n → Y₁, if c.decode₁ y = a then 0 else
      (W.receiver₁.block n).transition (fun t ↦ (c.encode₁ a t, c.encode₂ b t)) y
  let e₂ := (c.messages₁ * c.messages₂ : ℝ)⁻¹ *
    ∑ a, ∑ b, ∑ y : Fin n → Y₂, if c.decode₂ y = b then 0 else
      (W.receiver₂.block n).transition (fun t ↦ (c.encode₁ a t, c.encode₂ b t)) y
  exact max e₁ e₂

/-- The two sender rates in bits per physical interference-channel use. -/
noncomputable def rates {W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂} {n : ℕ}
    (c : Code W n) : RatePair :=
  (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n)

/-- Closed nonnegative rate region achievable with both average receiver errors vanishing. -/
noncomputable def capacityRegion (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) : Set RatePair :=
  Operational.achievableRegion (Code W) (fun _ _ ↦ True)
    (fun _ c ↦ error c) (fun _ c ↦ rates c)

/-- Both receivers use one conditional-product input law. -/
noncomputable def strongRegion (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) : Set RatePair :=
  closure {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ t : ℕ, ∃ p : FiniteDistribution (Fin t),
    ∃ a : FiniteChannel (Fin t) X₁, ∃ b : FiniteChannel (Fin t) X₂,
      let inputs := FiniteInformation.joint p (FiniteChannel.ofRows fun v ↦
        FiniteInformation.independent (a.rowDistribution v) (b.rowDistribution v))
      let q₁ := FiniteInformation.joint inputs (W.receiver₁.encoded Prod.snd)
      let q₂ := FiniteInformation.joint inputs (W.receiver₂.encoded Prod.snd)
      r.1 ≤ FiniteInformation.conditional q₁ (fun z ↦ z.1.2.1) Prod.snd
        (fun z ↦ (z.1.1, z.1.2.2)) ∧
      r.2 ≤ FiniteInformation.conditional q₂ (fun z ↦ z.1.2.2) Prod.snd
        (fun z ↦ (z.1.1, z.1.2.1)) ∧
      r.1 + r.2 ≤ FiniteInformation.conditional q₁ (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) ∧
      r.1 + r.2 ≤ FiniteInformation.conditional q₂ (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1)}

/-- Independent private/common auxiliaries and deterministic channel inputs. -/
structure HKData (X₁ X₂ : Type*) where
  /-- Size of the finite time-sharing alphabet. -/
  timeCard : ℕ
  /-- Common finite alphabet size used for the private and common auxiliaries. -/
  auxCard : ℕ
  /-- Distribution of the time-sharing variable. -/
  time : FiniteDistribution (Fin timeCard)
  /-- First sender's private auxiliary law conditioned on the time-sharing value. -/
  private₁ : FiniteChannel (Fin timeCard) (Fin auxCard)
  /-- First sender's common auxiliary law conditioned on the time-sharing value. -/
  common₁ : FiniteChannel (Fin timeCard) (Fin auxCard)
  /-- Second sender's private auxiliary law conditioned on the time-sharing value. -/
  private₂ : FiniteChannel (Fin timeCard) (Fin auxCard)
  /-- Second sender's common auxiliary law conditioned on the time-sharing value. -/
  common₂ : FiniteChannel (Fin timeCard) (Fin auxCard)
  /-- First channel input as a function of time sharing and its private/common auxiliaries. -/
  input₁ : Fin timeCard → Fin auxCard → Fin auxCard → X₁
  /-- Second channel input as a function of time sharing and its private/common auxiliaries. -/
  input₂ : Fin timeCard → Fin auxCard → Fin auxCard → X₂

/-- Joint auxiliary law with private and common variables conditionally independent given time sharing. -/
def HKData.law (a : HKData X₁ X₂) :=
  FiniteInformation.joint a.time (FiniteChannel.ofRows fun q ↦
    FiniteInformation.independent (a.private₁.rowDistribution q)
      (FiniteInformation.independent (a.common₁.rowDistribution q)
        (FiniteInformation.independent (a.private₂.rowDistribution q)
          (a.common₂.rowDistribution q))))

/-- Channel input pair obtained from the time-sharing and four private/common auxiliary values. -/
def HKData.inputs (a : HKData X₁ X₂)
    (z : Fin a.timeCard × Fin a.auxCard × Fin a.auxCard × Fin a.auxCard × Fin a.auxCard) :=
  (a.input₁ z.1 z.2.1 z.2.2.1, a.input₂ z.1 z.2.2.2.1 z.2.2.2.2)

/-- Retain selected auxiliary coordinates as optional values and erase the remaining coordinates. -/
noncomputable def selected {k : ℕ} (s : Finset (Fin 3)) (v : Fin 3 → Fin k) :
    Fin 3 → Option (Fin k) :=
  fun j ↦ if j ∈ s then some (v j) else none

/-- The seven nonempty-subset inequalities for a three-codebook decoder. -/
noncomputable def packingRegion {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    {q k : ℕ} (p : FiniteDistribution (Ω × Y))
    (time : Ω → Fin q) (observables : Ω → Fin 3 → Fin k) (r : Fin 3 → ℝ) : Prop :=
  ∀ s : Finset (Fin 3), s.Nonempty →
    (∑ j ∈ s, r j) ≤ FiniteInformation.conditional p
      (fun z ↦ selected s (observables z.1)) Prod.snd
      (fun z ↦ (time z.1, selected (Finset.univ \ s) (observables z.1)))

/-- Closed convex hull of rates satisfying both receivers' private/common-message packing constraints. -/
noncomputable def hanKobayashi (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) : Set RatePair :=
  closure (convexHull ℝ {r | ∃ a : HKData X₁ X₂, ∃ s₁ t₁ s₂ t₂ : ℝ,
    0 ≤ s₁ ∧ 0 ≤ t₁ ∧ 0 ≤ s₂ ∧ 0 ≤ t₂ ∧ r.1 = s₁ + t₁ ∧ r.2 = s₂ + t₂ ∧
    packingRegion (FiniteInformation.joint a.law (W.receiver₁.encoded a.inputs))
      Prod.fst (fun z ↦ ![z.2.1, z.2.2.1, z.2.2.2.2]) ![s₁, t₁, t₂] ∧
    packingRegion (FiniteInformation.joint a.law (W.receiver₂.encoded a.inputs))
      Prod.fst (fun z ↦ ![z.2.2.2.1, z.2.2.2.2, z.2.2.1]) ![s₂, t₂, t₁]})

/-- A fixed receiver-marginal coupling, legitimate because there is no feedback. -/
noncomputable def cutSet (W : FiniteInterferenceChannel X₁ X₂ Y₁ Y₂) : Set RatePair :=
  let V := FiniteChannel.ofRows fun x ↦ FiniteInformation.independent
    (W.receiver₁.rowDistribution x) (W.receiver₂.rowDistribution x)
  closure (convexHull ℝ {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ p : FiniteDistribution (X₁ × X₂), let q := FiniteInformation.joint p V
      r.1 ≤ FiniteInformation.conditional q (fun z ↦ z.1.1) Prod.snd (fun z ↦ z.1.2) ∧
      r.2 ≤ FiniteInformation.conditional q (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) ∧
      r.1 + r.2 ≤ FiniteInformation.information q Prod.fst Prod.snd})

end CapacityAtlas.Interference
