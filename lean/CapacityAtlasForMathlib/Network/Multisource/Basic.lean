/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi

open scoped BigOperators

namespace CapacityAtlas.Multisource

/-- A finite acyclic network with independently located message sources. -/
structure Network (vertices edges sources : ℕ) where
  source : Fin edges → Fin vertices
  target : Fin edges → Fin vertices
  increasing : ∀ e, (source e).val < (target e).val
  sourceNode : Fin sources → Fin vertices
  linkRate : Fin edges → ℝ
  linkRate_nonneg : ∀ e, 0 ≤ linkRate e
  sinks : Finset (Fin vertices)
  sinks_nonempty : sinks.Nonempty

namespace Network

variable {vertices edges sources : ℕ} (G : Network vertices edges sources)

noncomputable def packetBits (n : ℕ) (e : Fin edges) : ℕ :=
  Nat.floor ((n : ℝ) * G.linkRate e)

/-- A fixed binary packet budget; packet timing carries no information. -/
abbrev Packet (n : ℕ) (e : Fin edges) := Fin (2 ^ G.packetBits n e)

instance packetNonempty (n : ℕ) (e : Fin edges) : Nonempty (G.Packet n e) :=
  ⟨⟨0, Nat.two_pow_pos _⟩⟩

abbrev Message (messages : Fin sources → ℕ) := (i : Fin sources) → Fin (messages i)

/-- The locality conditions express deterministic functions of local messages
and incoming packets, including at sinks that host a source. -/
@[capacity_problem "noiseless-multisource-multicast-network", capacity_definition]
structure Code (n : ℕ) where
  messages : Fin sources → ℕ
  messages_pos : ∀ i, 0 < messages i
  packet : Message messages → (e : Fin edges) → G.Packet n e
  packet_local : ∀ e m m',
    (∀ i, G.sourceNode i = G.source e → m i = m' i) →
    (∀ a, G.target a = G.source e → packet m a = packet m' a) →
    packet m e = packet m' e
  decode : (v : Fin vertices) → v ∈ G.sinks → Message messages → Message messages
  decode_local : ∀ v hv m m',
    (∀ i, G.sourceNode i = v → m i = m' i) →
    (∀ a, G.target a = v → packet m a = packet m' a) →
    decode v hv m = decode v hv m'

namespace Code

variable {G} {n : ℕ} (c : G.Code n)

instance messageNonempty : Nonempty (Message c.messages) :=
  ⟨fun i ↦ ⟨0, c.messages_pos i⟩⟩

def Successful (m : Message c.messages) : Prop :=
  ∀ v, ∀ hv : v ∈ G.sinks, c.decode v hv m = m

noncomputable def successCount : ℕ := by
  classical
  exact Fintype.card {m : Message c.messages // c.Successful m}

/-- Joint average error for independent uniform source messages. -/
noncomputable def error : ℝ :=
  1 - (c.successCount : ℝ) / Fintype.card (Message c.messages)

noncomputable def rate (i : Fin sources) : ℝ :=
  Operational.messageRate (c.messages i) n

abbrev Observation (v : Fin vertices) :=
  ((i : {i : Fin sources // G.sourceNode i = v}) → Fin (c.messages i.val)) ×
  ((e : {e : Fin edges // G.target e = v}) → G.Packet n e.val)

def observe (v : Fin vertices) (m : Message c.messages) : c.Observation v :=
  (fun i ↦ m i.val, fun e ↦ c.packet m e.val)

/-- Locality gives actual local encoders on the full observation alphabet. -/
theorem exists_localEncode (e : Fin edges) :
    ∃ f : c.Observation (G.source e) → G.Packet n e,
      ∀ m, c.packet m e = f (c.observe (G.source e) m) := by
  have hf : Function.FactorsThrough (fun m ↦ c.packet m e) (c.observe (G.source e)) := by
    intro m m' h
    apply c.packet_local e m m'
    · intro i hi
      exact congrFun (congrArg Prod.fst h) ⟨i, hi⟩
    · intro a ha
      exact congrFun (congrArg Prod.snd h) ⟨a, ha⟩
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff _).mp hf
  exact ⟨f, fun m ↦ congrFun hf m⟩

theorem exists_localDecode (v : Fin vertices) (hv : v ∈ G.sinks) :
    ∃ f : c.Observation v → Message c.messages,
      ∀ m, c.decode v hv m = f (c.observe v m) := by
  have hf : Function.FactorsThrough (c.decode v hv) (c.observe v) := by
    intro m m' h
    apply c.decode_local v hv m m'
    · intro i hi
      exact congrFun (congrArg Prod.fst h) ⟨i, hi⟩
    · intro a ha
      exact congrFun (congrArg Prod.snd h) ⟨a, ha⟩
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff _).mp hf
  exact ⟨f, fun m ↦ congrFun hf m⟩

end Code

@[capacity_problem "noiseless-multisource-multicast-network", capacity_definition]
noncomputable def capacityRegion : Set (Fin sources → ℝ) :=
  Operational.achievableVectorRegion G.Code (fun _ _ ↦ True)
    (fun _ c ↦ c.error) (fun _ c ↦ c.rate)

noncomputable def cutRate (cut : Finset (Fin vertices)) : ℝ :=
  ∑ e : Fin edges, if G.source e ∈ cut ∧ G.target e ∉ cut then G.linkRate e else 0

noncomputable def cutDemand (cut : Finset (Fin vertices)) (r : Fin sources → ℝ) : ℝ :=
  ∑ i : Fin sources, if G.sourceNode i ∈ cut then r i else 0

def cutRegion : Set (Fin sources → ℝ) :=
  {r | (∀ i, 0 ≤ r i) ∧ ∀ v ∈ G.sinks, ∀ cut : Finset (Fin vertices),
    v ∉ cut → G.cutDemand cut r ≤ G.cutRate cut}

end Network
end CapacityAtlas.Multisource
