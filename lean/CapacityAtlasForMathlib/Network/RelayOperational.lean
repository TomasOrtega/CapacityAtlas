/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.CausalHistories
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion

open scoped BigOperators

namespace CapacityAtlas.Relay

variable {X R Z Y : Type*} [Fintype X] [Fintype R] [Fintype Z] [Fintype Y]

/-- Source input X, relay input R, relay observation Z, destination output Y. -/
abbrev Channel (X R Z Y : Type*) [Fintype X] [Fintype R] [Fintype Z] [Fintype Y] :=
  FiniteChannel (X × R) (Z × Y)

/-- No source feedback. The relay sees only strictly past observations. -/
structure Code (W : Channel X R Z Y) (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → Fin n → X
  relay : (t : Fin n) → (Fin t.val → Z) → R
  decode : (Fin n → Y) → Fin messages

noncomputable def error {W : Channel X R Z Y} {n : ℕ} (c : Code W n) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m, ∑ z : Fin n → Z, ∑ y : Fin n → Y,
    if c.decode y = m then 0 else
      ∏ t, W.transition (c.encode m t, c.relay t (CausalHistories.past z t)) (z t, y t)

noncomputable def rate {W : Channel X R Z Y} {n : ℕ} (c : Code W n) :=
  Operational.messageRate c.messages n

noncomputable def capacity (W : Channel X R Z Y) : ℝ :=
  Operational.capacity (Code W) (fun _ _ ↦ True) (fun _ c ↦ error c) (fun _ c ↦ rate c)

/-- Conditional on the relay input, X-Z-Y is a Markov chain. -/
def IsDegraded (W : Channel X R Z Y) : Prop :=
  ∃ relay : FiniteChannel (X × R) Z, ∃ destination : FiniteChannel (Z × R) Y,
    ∀ x r z y, W.transition (x, r) (z, y) =
      relay.transition (x, r) z * destination.transition (z, r) y

noncomputable def decodeForward (W : Channel X R Z Y) : ℝ :=
  sSup {rate | ∃ p : FiniteDistribution (X × R),
    let q := FiniteInformation.joint p W
    rate = min
      (FiniteInformation.conditional q (fun a ↦ a.1.1) (fun a ↦ a.2.1) (fun a ↦ a.1.2))
      (FiniteInformation.information q Prod.fst (fun a ↦ a.2.2))}

noncomputable def cutSet (W : Channel X R Z Y) : ℝ :=
  sSup {rate | ∃ p : FiniteDistribution (X × R),
    let q := FiniteInformation.joint p W
    rate = min
      (FiniteInformation.conditional q (fun a ↦ a.1.1) Prod.snd (fun a ↦ a.1.2))
      (FiniteInformation.information q Prod.fst (fun a ↦ a.2.2))}

/-- Compress-and-forward with destination side information. -/
noncomputable def compressForward (W : Channel X R Z Y) : ℝ :=
  sSup {rate | ∃ p : FiniteDistribution X, ∃ r : FiniteDistribution R,
    ∃ k : ℕ, ∃ quantize : FiniteChannel (Z × R) (Fin k),
      let q := FiniteInformation.joint (FiniteInformation.independent p r) W
      let joint := FiniteInformation.joint q
        (quantize.encoded fun a ↦ (a.2.1, a.1.2))
      FiniteInformation.conditional joint (fun a ↦ a.1.2.1) Prod.snd
          (fun a ↦ (a.1.1.2, a.1.2.2)) ≤
        FiniteInformation.information q (fun a ↦ a.1.2) (fun a ↦ a.2.2) ∧
      rate = FiniteInformation.conditional joint (fun a ↦ a.1.1.1)
        (fun a ↦ (a.1.2.2, a.2)) (fun a ↦ a.1.1.2)}

end CapacityAtlas.Relay
