/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.WirelessTransport.Operations
import CapacityAtlasUtil.Metadata

open scoped BigOperators

namespace CapacityAtlas.Tests

open WirelessTransport

noncomputable section

private def linePoint (x : ℝ) : Point := WithLp.toLp 2 ![x, 0]

private theorem linePoint_dist (x y : ℝ) : dist (linePoint x) (linePoint y) = |x - y| := by
  simp [linePoint, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq,
    Real.sqrt_sq_eq_abs]

private def detourPosition (v : Fin 3) : Point := linePoint (![0, 1, 1 / 2] v)

private def detourPattern (s : Fin 2) : Pattern (Fin 3) detourPosition 1 where
  Link := Fin 1
  finiteLink := inferInstance
  sender := fun _ => if s = 0 then 0 else 1
  receiver := fun _ => if s = 0 then 1 else 2
  sender_injective := fun _ _ _ => Subsingleton.elim _ _
  protocol := fun _ _ h => (h (Subsingleton.elim _ _)).elim

private def detourSchedule : Schedule (Fin 3) detourPosition 1 1 where
  slots := 2
  bands := 1
  duration := fun _ => 1 / 2
  duration_nonneg := fun _ => by norm_num
  duration_sum := by norm_num
  bandRate := fun _ => 1
  bandRate_nonneg := fun _ => zero_le_one
  bandRate_sum := by norm_num
  pattern := fun s _ => detourPattern s

private def detourExecution : Execution (Fin 3) detourPosition 1 1 where
  schedule := detourSchedule
  Packet := Fin 1
  finitePacket := inferInstance
  amount := fun _ => 1 / 2
  amount_nonneg := fun _ => by norm_num
  integralAmounts := ⟨2, by norm_num, fun _ => ⟨1, by norm_num⟩⟩
  destination := fun _ => 2
  hops := fun _ => 2
  route := fun _ k => if k = 0 then 0 else if k = 1 then 1 else 2
  delivered := fun _ => by norm_num
  resource := fun _ h => ⟨h, (0 : Fin 1), (0 : Fin 1)⟩
  causal := fun _ _ _ h => h
  hop_sender := by
    intro p h
    change (if h = 0 then (0 : Fin 3) else 1) =
      (if h.val = 0 then 0 else if h.val = 1 then 1 else 2)
    fin_cases h <;> decide
  hop_receiver := by
    intro p h
    change (if h = 0 then (1 : Fin 3) else 2) =
      (if h.val + 1 = 0 then 0 else if h.val + 1 = 1 then 1 else 2)
    fin_cases h <;> decide
  load_le := by
    classical
    dsimp only [detourSchedule, detourPattern, Schedule.Resource, Schedule.available]
    intro r
    change _ ≤ (1 / 2 : ℝ) * 1
    rcases r with ⟨s, b, l⟩
    fin_cases s <;> fin_cases b <;> fin_cases l <;>
      norm_num [Fin.sum_univ_succ]

/-- A detour earns endpoint distance once, not the sum of its hop lengths. -/
@[capacity_test]
theorem wireless_detour_transport : detourExecution.transportRate = 1 / 4 := by
  dsimp only [Execution.transportRate, detourExecution, detourPosition]
  norm_num [linePoint_dist, Matrix.cons_val_two]

@[capacity_test]
theorem wireless_detour_hop_work :
    (∑ h : Fin 2, (1 / 2 : ℝ) *
      detourSchedule.length (detourExecution.resource (0 : Fin 1) h)) =
      3 / 4 := by
  dsimp only [Schedule.length, Schedule.sender, Schedule.receiver, detourExecution,
    detourSchedule, detourPattern, detourPosition]
  norm_num [Fin.sum_univ_succ, linePoint_dist, Matrix.cons_val_two]

@[capacity_test]
theorem wireless_no_instantaneous_relay {V : Type} {position : V → Point} {Δ W : ℝ}
    (E : Execution V position Δ W) (hslot : E.schedule.slots = 1) (p : E.Packet) :
    E.hops p ≤ 1 := by
  have h := Fintype.card_le_of_injective _ (E.causal p).injective
  simpa [hslot] using h

@[capacity_test]
theorem wireless_receiver_cannot_transmit {V : Type} {position : V → Point} {Δ : ℝ}
    (hΔ : 0 < Δ) (P : Pattern V position Δ) {i j : P.Link} (hij : i ≠ j)
    (hpositive : 0 < dist (position (P.sender i)) (position (P.receiver i))) :
    P.sender j ≠ P.receiver i := by
  intro hsame
  have h := P.protocol i j hij
  rw [hsame, dist_self] at h
  nlinarith

@[capacity_test]
theorem wireless_zero_bandwidth_delivers_zero {V : Type} {position : V → Point} {Δ : ℝ}
    (E : Execution V position Δ 0) : E.transportRate = 0 := by
  have hband (b : Fin E.schedule.bands) : E.schedule.bandRate b = 0 := by
    apply le_antisymm _ (E.schedule.bandRate_nonneg b)
    exact (Finset.single_le_sum (fun b _ => E.schedule.bandRate_nonneg b)
      (Finset.mem_univ b)).trans E.schedule.bandRate_sum
  apply le_antisymm _ E.transportRate_nonneg
  simpa [Schedule.available, hband] using E.transportRate_le_hopWork

end

end CapacityAtlas.Tests
