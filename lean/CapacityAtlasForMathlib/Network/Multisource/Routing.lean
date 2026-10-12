/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.LinearModel
import CapacityAtlasForMathlib.Network.LinearMulticast.Routing
import CapacityAtlasForMathlib.Network.FlowMultisource

open scoped BigOperators Classical

namespace CapacityAtlas.Multisource.Network

variable {vertices edges sources : ℕ} (G : Network vertices edges sources)

/-- Integer source demands satisfy every sink-separating directed cut. -/
def IntegerCutFeasible (cap : Fin edges → ℕ) (demand : Fin sources → ℕ) : Prop :=
  ∀ v ∈ G.sinks, ∀ S : Finset (Fin vertices), v ∉ S →
    (∑ i, if G.sourceNode i ∈ S then demand i else 0) ≤
      ∑ e, if G.source e ∈ S ∧ G.target e ∉ S then cap e else 0

/-- Each path delivers one independent source scalar. -/
theorem exists_routing_of_packing (cap : Fin edges → ℕ) (demand : Fin sources → ℕ)
    (v : Fin vertices) (paths : Input demand → List (Wire cap))
    (hroutes : ∀ i, NetworkFlow.Route (fun e : Wire cap ↦ G.source e.1)
      (fun e : Wire cap ↦ G.target e.1) (G.sourceNode i.1) v (paths i))
    (hcap : ∀ e, (∑ i, (paths i).count e) ≤ 1) :
    ∃ output : Input demand → Input demand ⊕ Wire cap,
      (∀ i, G.PortAt cap demand v (output i)) ∧
      Nonempty ((G.linearCircuit cap demand).Routing output) := by
  let output : Input demand → Input demand ⊕ Wire cap := fun i ↦
    if h : paths i = [] then Sum.inl i else Sum.inr ((paths i).getLast h)
  have hdisjoint : ∀ e i j, e ∈ paths i → e ∈ paths j → i = j := by
    intro e i j hi hj
    exact ((Finset.sum_le_one_iff.mp (hcap e)) i j (Finset.mem_univ _)
      (Finset.mem_univ _) (Nat.ne_of_gt (List.count_pos_iff.mpr hi))
      (Nat.ne_of_gt (List.count_pos_iff.mpr hj))).1
  refine ⟨output, ?_, ⟨(G.linearCircuit cap demand).routingOfPaths output paths hdisjoint ?_ ?_⟩⟩
  · intro i
    dsimp only [output]
    split_ifs with h
    · have hh := hroutes i
      simpa only [h, NetworkFlow.Route, PortAt] using hh
    · exact (hroutes i).last_target h
  · intro i e he
    obtain hi | ⟨p, hp, hpe⟩ := (hroutes i).source_or_predecessor he
    · exact Or.inl hi.symm
    · exact Or.inr ⟨p, hp, hpe⟩
  · intro i
    dsimp only [output]
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, List.getLast_mem h⟩

/-- Integral cut feasibility yields a routing witness separately for each sink. -/
theorem exists_routing_of_integerCuts (cap : Fin edges → ℕ) (demand : Fin sources → ℕ)
    (hcut : G.IntegerCutFeasible cap demand) (v : Fin vertices) (hv : v ∈ G.sinks) :
    ∃ output : Input demand → Input demand ⊕ Wire cap,
      (∀ i, G.PortAt cap demand v (output i)) ∧
      Nonempty ((G.linearCircuit cap demand).Routing output) := by
  have hunit : ∀ S : Finset (Fin vertices), v ∉ S →
      (∑ i : Input demand, if G.sourceNode i.1 ∈ S then 1 else 0) ≤
        NetworkFlow.cutCapacity (fun e : Wire cap ↦ G.source e.1)
          (fun e : Wire cap ↦ G.target e.1) (fun _ ↦ 1) S := by
    intro S hS
    have hi : (∑ i : Input demand, if G.sourceNode i.1 ∈ S then 1 else 0) =
        ∑ i, if G.sourceNode i ∈ S then demand i else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    have he : NetworkFlow.cutCapacity (fun e : Wire cap ↦ G.source e.1)
        (fun e : Wire cap ↦ G.target e.1) (fun _ ↦ 1) S =
        ∑ e, if G.source e ∈ S ∧ G.target e ∉ S then cap e else 0 := by
      unfold NetworkFlow.cutCapacity
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    rw [hi, he]
    exact hcut v hv S hS
  obtain ⟨paths, hr, hb⟩ := NetworkFlow.multisource_route_packing
    (fun e : Wire cap ↦ G.source e.1) (fun e : Wire cap ↦ G.target e.1)
    (fun i : Input demand ↦ G.sourceNode i.1) (fun _ ↦ 1) v hunit
  exact G.exists_routing_of_packing cap demand v paths (fun i ↦ (hr i).1) hb

/-- One finite binary extension field serves all sinks simultaneously. -/
theorem exists_linear_of_integerCuts (cap : Fin edges → ℕ) (demand : Fin sources → ℕ)
    (hcut : G.IntegerCutFeasible cap demand) :
    ∃ b : ℕ, 0 < b ∧ ∃ coeff : (G.linearCircuit cap demand).Variable → GaloisField 2 b,
      ∃ output : {v : Fin vertices // v ∈ G.sinks} → Input demand → Input demand ⊕ Wire cap,
        (∀ t i, G.PortAt cap demand t.val (output t i)) ∧
        ∀ t, ((G.linearCircuit cap demand).outputMatrix coeff (output t)).det ≠ 0 := by
  have hr : ∀ t : {v : Fin vertices // v ∈ G.sinks},
      ∃ output : Input demand → Input demand ⊕ Wire cap,
        (∀ i, G.PortAt cap demand t.val (output i)) ∧
        Nonempty ((G.linearCircuit cap demand).Routing output) :=
    fun t ↦ G.exists_routing_of_integerCuts cap demand hcut t.val t.property
  choose output hlocal routes using hr
  obtain ⟨b, hb, coeff, hdet⟩ := (G.linearCircuit cap demand).simultaneous_of_routing
    output (fun t ↦ Classical.choice (routes t))
  exact ⟨b, hb, coeff, output, hlocal, hdet⟩

end CapacityAtlas.Multisource.Network
