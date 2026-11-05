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
  /-- Index type of links active simultaneously on the band. -/
  Link : Type
  /-- Finite enumeration of the active links. -/
  finiteLink : Fintype Link
  /-- Transmitting node of each active link. -/
  sender : Link → V
  /-- Receiving node of each active link. -/
  receiver : Link → V
  /-- Each node transmits on at most one active link in this pattern. -/
  sender_injective : Function.Injective sender
  /-- Every other transmitter lies outside the receiver guard region of an active link. -/
  protocol : ∀ i j, i ≠ j →
    (1 + Δ) * dist (position (sender i)) (position (receiver i)) ≤
      dist (position (sender j)) (position (receiver i))

attribute [instance] Pattern.finiteLink

/-- Slot durations are fractions of the observation interval; unused time is idle. -/
structure Schedule (V : Type) (position : V → Point) (Δ W : ℝ) where
  /-- Number of scheduled time slots. -/
  slots : ℕ
  /-- Number of frequency bands used by the schedule. -/
  bands : ℕ
  /-- Fraction of the observation interval allocated to each slot. -/
  duration : Fin slots → ℝ
  /-- Slot durations are nonnegative. -/
  duration_nonneg : ∀ s, 0 ≤ duration s
  /-- The total scheduled duration does not exceed the observation interval. -/
  duration_sum : ∑ s, duration s ≤ 1
  /-- Bit service rate assigned to each frequency band. -/
  bandRate : Fin bands → ℝ
  /-- Band service rates are nonnegative. -/
  bandRate_nonneg : ∀ b, 0 ≤ bandRate b
  /-- The sum of band service rates does not exceed the bandwidth budget W. -/
  bandRate_sum : ∑ b, bandRate b ≤ W
  /-- Simultaneous feasible link pattern in each time-slot and frequency-band pair. -/
  pattern : Fin slots → Fin bands → Pattern V position Δ

namespace Schedule

variable {V : Type} {position : V → Point} {Δ W : ℝ}

/-- A scheduled transmission identified by its time slot, frequency band, and simultaneous link. -/
abbrev Resource (S : Schedule V position Δ W) :=
  (s : Fin S.slots) × (b : Fin S.bands) × (S.pattern s b).Link

instance (S : Schedule V position Δ W) : Fintype S.Resource :=
  inferInstanceAs (Fintype ((s : Fin S.slots) × (b : Fin S.bands) × (S.pattern s b).Link))

/-- Transmitting node assigned to a scheduled link resource. -/
def sender (S : Schedule V position Δ W) (r : S.Resource) : V :=
  (S.pattern r.1 r.2.1).sender r.2.2

/-- Receiving node assigned to a scheduled link resource. -/
def receiver (S : Schedule V position Δ W) (r : S.Resource) : V :=
  (S.pattern r.1 r.2.1).receiver r.2.2

/-- Euclidean sender-to-receiver distance of a scheduled link resource. -/
def length (S : Schedule V position Δ W) (r : S.Resource) : ℝ :=
  dist (position (S.sender r)) (position (S.receiver r))

/-- Bit service available on a resource, equal to its slot duration times its band rate. -/
def available (S : Schedule V position Δ W) (r : S.Resource) : ℝ :=
  S.duration r.1 * S.bandRate r.2.1

end Schedule

/-- A finite collection of delivered packets with causal store-and-forward routes.
Amounts are bit counts divided by a common positive observation time. -/
@[capacity_problem "wireless-network-transport-capacity", capacity_definition]
structure Execution (V : Type) (position : V → Point) (Δ W : ℝ) where
  /-- Time and frequency resources supporting the packet transmissions. -/
  schedule : Schedule V position Δ W
  /-- Index type of delivered packets. -/
  Packet : Type
  /-- Finite enumeration of the delivered packets. -/
  finitePacket : Fintype Packet
  /-- Packet bit count divided by the common observation time. -/
  amount : Packet → ℝ
  /-- Every packet carries a nonnegative amount of data. -/
  amount_nonneg : ∀ p, 0 ≤ amount p
  /-- A common positive observation time makes every packet amount an integer bit count. -/
  integralAmounts : ∃ T : ℝ, 0 < T ∧ ∀ p, ∃ k : ℕ, amount p * T = k
  /-- Destination assigned to each originating node. -/
  destination : V → V
  /-- Number of transmission hops on each packet route. -/
  hops : Packet → ℕ
  /-- Sequence of nodes visited by each packet, starting at its originating node. -/
  route : Packet → ℕ → V
  /-- Each route ends at the destination of its originating node. -/
  delivered : ∀ p, route p (hops p) = destination (route p 0)
  /-- Scheduled link resource assigned to each packet hop. -/
  resource : (p : Packet) → Fin (hops p) → schedule.Resource
  /-- A packet's successive hops occur in strictly increasing time slots. -/
  causal : ∀ p, StrictMono fun h => (resource p h).1
  /-- The resource sender agrees with the packet's current route node. -/
  hop_sender : ∀ p h, schedule.sender (resource p h) = route p h.val
  /-- The resource receiver agrees with the packet's next route node. -/
  hop_receiver : ∀ p h, schedule.receiver (resource p h) = route p (h.val + 1)
  /-- Total packet load assigned to a resource does not exceed its available bit service. -/
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

/-- Supremum of achievable transport rates under the node, radius, interference, and bandwidth budgets. -/
@[capacity_problem "wireless-network-transport-capacity", capacity_definition]
def capacity (n : ℕ) (R Δ W : ℝ) : ℝ := sSup {t | Achievable n R Δ W t}

end

end CapacityAtlas.WirelessTransport
