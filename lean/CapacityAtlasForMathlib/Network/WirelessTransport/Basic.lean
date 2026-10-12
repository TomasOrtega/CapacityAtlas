/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.WirelessTransport.Geometry
import CapacityAtlasUtil

open scoped BigOperators

namespace CapacityAtlas.WirelessTransport

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Simultaneous unicast links on one frequency band. -/
structure Pattern (V : Type) (position : V → Point) (Δ : ℝ) where
  Link : Type
  finiteLink : Fintype Link
  sender : Link → V
  receiver : Link → V
  sender_injective : Function.Injective sender
  protocol : ∀ i j, i ≠ j →
    (1 + Δ) * dist (position (sender i)) (position (receiver i)) ≤
      dist (position (sender j)) (position (receiver i))

attribute [instance] Pattern.finiteLink

/-- Slot durations are fractions of the observation interval; unused time is idle. -/
structure Schedule (V : Type) (position : V → Point) (Δ W : ℝ) where
  slots : ℕ
  bands : ℕ
  duration : Fin slots → ℝ
  duration_nonneg : ∀ s, 0 ≤ duration s
  duration_sum : ∑ s, duration s ≤ 1
  bandRate : Fin bands → ℝ
  bandRate_nonneg : ∀ b, 0 ≤ bandRate b
  bandRate_sum : ∑ b, bandRate b ≤ W
  pattern : Fin slots → Fin bands → Pattern V position Δ

namespace Schedule

variable {V : Type} {position : V → Point} {Δ W : ℝ}

abbrev Resource (S : Schedule V position Δ W) :=
  (s : Fin S.slots) × (b : Fin S.bands) × (S.pattern s b).Link

instance (S : Schedule V position Δ W) : Fintype S.Resource :=
  inferInstanceAs (Fintype ((s : Fin S.slots) × (b : Fin S.bands) × (S.pattern s b).Link))

def sender (S : Schedule V position Δ W) (r : S.Resource) : V :=
  (S.pattern r.1 r.2.1).sender r.2.2

def receiver (S : Schedule V position Δ W) (r : S.Resource) : V :=
  (S.pattern r.1 r.2.1).receiver r.2.2

def length (S : Schedule V position Δ W) (r : S.Resource) : ℝ :=
  dist (position (S.sender r)) (position (S.receiver r))

def available (S : Schedule V position Δ W) (r : S.Resource) : ℝ :=
  S.duration r.1 * S.bandRate r.2.1

end Schedule

/-- A finite collection of delivered packets with causal store-and-forward routes.
Amounts are bit counts divided by a common positive observation time. -/
@[capacity_problem "wireless-network-transport-capacity", capacity_definition]
structure Execution (V : Type) (position : V → Point) (Δ W : ℝ) where
  schedule : Schedule V position Δ W
  Packet : Type
  finitePacket : Fintype Packet
  amount : Packet → ℝ
  amount_nonneg : ∀ p, 0 ≤ amount p
  integralAmounts : ∃ T : ℝ, 0 < T ∧ ∀ p, ∃ k : ℕ, amount p * T = k
  destination : V → V
  hops : Packet → ℕ
  route : Packet → ℕ → V
  delivered : ∀ p, route p (hops p) = destination (route p 0)
  resource : (p : Packet) → Fin (hops p) → schedule.Resource
  causal : ∀ p, StrictMono fun h => (resource p h).1
  hop_sender : ∀ p h, schedule.sender (resource p h) = route p h.val
  hop_receiver : ∀ p h, schedule.receiver (resource p h) = route p (h.val + 1)
  load_le : ∀ r : schedule.Resource,
    (∑ p, ∑ h : Fin (hops p), if resource p h = r then amount p else 0) ≤
      schedule.available r

attribute [instance] Execution.finitePacket

namespace Execution

variable {V : Type} {position : V → Point} {Δ W : ℝ}

/-- Each packet is credited once, using its endpoints rather than its route length. -/
def transportRate (E : Execution V position Δ W) : ℝ :=
  ∑ p, E.amount p * dist (position (E.route p 0)) (position (E.route p (E.hops p)))

theorem transportRate_nonneg (E : Execution V position Δ W) : 0 ≤ E.transportRate := by
  exact Finset.sum_nonneg fun p _ => mul_nonneg (E.amount_nonneg p) dist_nonneg

end Execution

/-- The node budget includes unused nodes, which may be added without changing a schedule. -/
def Achievable (n : ℕ) (R Δ W t : ℝ) : Prop :=
  ∃ (V : Type) (_ : Fintype V), Fintype.card V ≤ n ∧
    ∃ position : V → Point, (∀ v, ‖position v‖ ≤ R) ∧
      ∃ E : Execution V position Δ W, E.transportRate = t

@[capacity_problem "wireless-network-transport-capacity", capacity_definition]
def capacity (n : ℕ) (R Δ W : ℝ) : ℝ := sSup {t | Achievable n R Δ W t}

end

end CapacityAtlas.WirelessTransport
