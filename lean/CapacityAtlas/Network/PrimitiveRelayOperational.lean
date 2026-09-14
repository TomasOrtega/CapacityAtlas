/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlas.Network.PrimitiveRelay
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.CausalHistories
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators

namespace CapacityAtlas.Network.PrimitiveRelayChannel

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Fixed bit-pipe schedule: floor(n R0) bits over n physical uses. -/
noncomputable def slotBits (W : PrimitiveRelayChannel X Y Z) (t : ℕ) : ℕ :=
  Nat.floor (((t + 1 : ℕ) : ℝ) * W.relayLinkCapacityBits) -
    Nat.floor ((t : ℝ) * W.relayLinkCapacityBits)

structure Code (W : PrimitiveRelayChannel X Y Z) (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → Fin n → X
  relay : (t : Fin n) → (Fin t.val → Z) → Fin (W.slotBits t.val) → Bool
  decode : (Fin n → Y) → ((t : Fin n) → Fin (W.slotBits t.val) → Bool) → Fin messages

noncomputable def error {W : PrimitiveRelayChannel X Y Z} {n : ℕ} (c : Code W n) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m, ∑ yz : Fin n → Y × Z,
    if c.decode (fun t ↦ (yz t).1)
      (fun t ↦ c.relay t (CausalHistories.past (fun k ↦ (yz k).2) t)) = m then 0 else
        (W.broadcast.block n).transition (c.encode m) yz

noncomputable def operationalCapacity (W : PrimitiveRelayChannel X Y Z) : ℝ :=
  Operational.capacity (Code W) (fun _ _ ↦ True) (fun _ c ↦ error c)
    (fun n c ↦ Operational.messageRate c.messages n)

noncomputable def cutSet (W : PrimitiveRelayChannel X Y Z) : ℝ :=
  sSup (Set.range fun p : FiniteDistribution X ↦
    let q := FiniteInformation.joint p W.broadcast
    min (FiniteInformation.information q Prod.fst Prod.snd)
      (FiniteInformation.information q Prod.fst (fun a ↦ a.2.1) + W.relayLinkCapacityBits))

noncomputable def compressForward (W : PrimitiveRelayChannel X Y Z) : ℝ :=
  sSup {r | ∃ p : FiniteDistribution X, ∃ k : ℕ, ∃ V : FiniteChannel Z (Fin k),
    let q := FiniteInformation.joint (FiniteInformation.joint p W.broadcast)
      (V.encoded fun a ↦ a.2.2)
    FiniteInformation.conditional q (fun a ↦ a.1.2.2) Prod.snd (fun a ↦ a.1.2.1) ≤
      W.relayLinkCapacityBits ∧
    r = FiniteInformation.information q (fun a ↦ a.1.1) (fun a ↦ (a.1.2.1, a.2))}

end CapacityAtlas.Network.PrimitiveRelayChannel
