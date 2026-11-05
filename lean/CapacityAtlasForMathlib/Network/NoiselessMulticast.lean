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
  /-- There is a vertex with index zero to serve as the source. -/
  vertices_pos : 0 < vertices
  /-- Tail vertex of each directed edge. -/
  source : Fin edges → Fin vertices
  /-- Head vertex of each directed edge. -/
  target : Fin edges → Fin vertices
  /-- Every edge follows the strict topological ordering of vertex indices. -/
  increasing : ∀ e, (source e).val < (target e).val
  /-- Capacity of each edge in bits per network use. -/
  linkRate : Fin edges → ℝ
  /-- Every edge capacity is nonnegative. -/
  linkRate_nonneg : ∀ e, 0 ≤ linkRate e
  /-- Vertices required to recover the source message. -/
  sinks : Finset (Fin vertices)
  /-- At least one sink is designated. -/
  sinks_nonempty : sinks.Nonempty
  /-- No designated sink is the source vertex. -/
  sinks_not_source : ∀ v ∈ sinks, v.val ≠ 0

namespace Network

variable {vertices edges : ℕ} (G : Network vertices edges)

/-- Distinguished source vertex with index zero. -/
def root : Fin vertices := ⟨0, G.vertices_pos⟩

/-- Binary words fitting an edge's rounded bit budget over n network uses. -/
noncomputable def Packet (n : ℕ) (e : Fin edges) :=
  Fin (Nat.floor ((n : ℝ) * G.linkRate e)) → Bool

/-- Only the source can evaluate the proof-indexed message argument. Other
nodes use exclusively incoming packets. There is no timing side channel. -/
structure Code (n : ℕ) where
  /-- Number of source messages. -/
  messages : ℕ
  /-- The source-message alphabet is nonempty. -/
  messages_pos : 0 < messages
  /-- Local edge encoder using incoming packets and source-message access only at the source. -/
  localEncode : (e : Fin edges) → (G.source e = G.root → Fin messages) →
    ((a : Fin edges) → G.target a = G.source e → G.Packet n a) → G.Packet n e
  /-- Sink decoder operating on the packets entering that sink. -/
  decode : (v : Fin vertices) → v ∈ G.sinks →
    ((a : Fin edges) → G.target a = v → G.Packet n a) → Fin messages

/-- Evaluate the code's edge packets in topological vertex order for a source message. -/
noncomputable def packets {n : ℕ} (c : G.Code n) (m : Fin c.messages) :
    (e : Fin edges) → G.Packet n e :=
  (List.finRange vertices).foldl
    (fun previous v e ↦ if G.source e = v then
      c.localEncode e (fun _ ↦ m) (fun a _ ↦ previous a) else previous e)
    (fun _ _ ↦ false)

/-- Fraction of source messages for which at least one designated sink decodes incorrectly. -/
noncomputable def error {n : ℕ} (c : G.Code n) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m,
    if ∀ v, ∀ hv : v ∈ G.sinks,
      c.decode v hv (fun a _ ↦ G.packets c m a) = m then 0 else 1

/-- Vanishing-average-error multicast capacity in bits per network use. -/
noncomputable def capacity : ℝ :=
  Operational.capacity G.Code (fun _ _ ↦ True) (fun _ c ↦ G.error c)
    (fun n c ↦ Operational.messageRate c.messages n)

/-- Total link capacity of edges leaving a chosen vertex cut. -/
noncomputable def cutRate (cut : Finset (Fin vertices)) : ℝ :=
  ∑ e : Fin edges, if G.source e ∈ cut ∧ G.target e ∉ cut then G.linkRate e else 0

/-- Infimum of cut capacities separating the source from any designated sink. -/
noncomputable def minCut : ℝ :=
  sInf {r | ∃ v ∈ G.sinks, ∃ cut : Finset (Fin vertices),
    G.root ∈ cut ∧ v ∉ cut ∧ r = G.cutRate cut}

end Network

end CapacityAtlas.NoiselessMulticast
