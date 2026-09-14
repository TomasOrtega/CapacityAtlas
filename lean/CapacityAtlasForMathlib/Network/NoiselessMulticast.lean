/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators

namespace CapacityAtlas.NoiselessMulticast

/-- A topologically ordered acyclic network. Vertex zero is the source. -/
structure Network (vertices edges : ℕ) where
  vertices_pos : 0 < vertices
  source : Fin edges → Fin vertices
  target : Fin edges → Fin vertices
  increasing : ∀ e, (source e).val < (target e).val
  linkRate : Fin edges → ℝ
  linkRate_nonneg : ∀ e, 0 ≤ linkRate e
  sinks : Finset (Fin vertices)
  sinks_nonempty : sinks.Nonempty
  sinks_not_source : ∀ v ∈ sinks, v.val ≠ 0

namespace Network

variable {vertices edges : ℕ} (G : Network vertices edges)

def root : Fin vertices := ⟨0, G.vertices_pos⟩

noncomputable def Packet (n : ℕ) (e : Fin edges) :=
  Fin (Nat.floor ((n : ℝ) * G.linkRate e)) → Bool

/-- Only the source can evaluate the proof-indexed message argument. Other
nodes use exclusively incoming packets. There is no timing side channel. -/
structure Code (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  localEncode : (e : Fin edges) → (G.source e = G.root → Fin messages) →
    ((a : Fin edges) → G.target a = G.source e → G.Packet n a) → G.Packet n e
  decode : (v : Fin vertices) → v ∈ G.sinks →
    ((a : Fin edges) → G.target a = v → G.Packet n a) → Fin messages

noncomputable def packets {n : ℕ} (c : G.Code n) (m : Fin c.messages) :
    (e : Fin edges) → G.Packet n e :=
  (List.finRange vertices).foldl
    (fun previous v e ↦ if G.source e = v then
      c.localEncode e (fun _ ↦ m) (fun a _ ↦ previous a) else previous e)
    (fun _ _ ↦ false)

noncomputable def error {n : ℕ} (c : G.Code n) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m,
    if ∀ v, ∀ hv : v ∈ G.sinks,
      c.decode v hv (fun a _ ↦ G.packets c m a) = m then 0 else 1

noncomputable def capacity : ℝ :=
  Operational.capacity G.Code (fun _ _ ↦ True) (fun _ c ↦ G.error c)
    (fun n c ↦ Operational.messageRate c.messages n)

noncomputable def cutRate (cut : Finset (Fin vertices)) : ℝ :=
  ∑ e : Fin edges, if G.source e ∈ cut ∧ G.target e ∉ cut then G.linkRate e else 0

noncomputable def minCut : ℝ :=
  sInf {r | ∃ v ∈ G.sinks, ∃ cut : Finset (Fin vertices),
    G.root ∈ cut ∧ v ∉ cut ∧ r = G.cutRate cut}

end Network

end CapacityAtlas.NoiselessMulticast
