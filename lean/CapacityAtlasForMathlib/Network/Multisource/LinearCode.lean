/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.LinearModel
import CapacityAtlasForMathlib.Network.LinearMulticast.Evaluation
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators Classical

namespace CapacityAtlas.Multisource.Network

variable {vertices edges sources : ℕ} (G : Multisource.Network vertices edges sources)

variable {K : Type} [Fintype K] {b : ℕ} (hcard : Fintype.card K = 2 ^ b)

noncomputable def vectorEquiv (k : ℕ) : (Fin k → K) ≃ Fin (2 ^ (b * k)) :=
  Fintype.equivFinOfCardEq (by simp [hcard, ← pow_mul])

noncomputable def inputSymbols (demand : Fin sources → ℕ)
    (m : Message (fun i ↦ 2 ^ (b * demand i))) : Input demand → K :=
  fun i ↦ (vectorEquiv hcard (demand i.1)).symm (m i.1) i.2

theorem inputSymbols_injective (demand : Fin sources → ℕ) :
    Function.Injective (inputSymbols hcard demand) := by
  intro m m' h
  funext i
  apply (vectorEquiv hcard (demand i)).symm.injective
  funext j
  exact congrFun h ⟨i, j⟩

noncomputable def packedPacket (cap : Fin edges → ℕ) {N : ℕ}
    (hbits : ∀ e, b * cap e ≤ G.packetBits N e) (e : Fin edges)
    (x : Fin (cap e) → K) : G.Packet N e :=
  Fin.castLE (Nat.pow_le_pow_right (by omega : 0 < 2) (hbits e))
    (vectorEquiv hcard (cap e) x)

theorem packedPacket_injective (cap : Fin edges → ℕ) {N : ℕ}
    (hbits : ∀ e, b * cap e ≤ G.packetBits N e) (e : Fin edges) :
    Function.Injective (G.packedPacket hcard cap hbits e) := by
  exact (Fin.castLE_injective _).comp (vectorEquiv hcard (cap e)).injective

include hcard in
theorem exists_perfectCode_of_linear [Field K] (cap : Fin edges → ℕ) (demand : Fin sources → ℕ)
    {N : ℕ} (hbits : ∀ e, b * cap e ≤ G.packetBits N e)
    (coeff : (G.linearCircuit cap demand).Variable → K)
    (output : {v : Fin vertices // v ∈ G.sinks} → Input demand → Input demand ⊕ Wire cap)
    (hlocal : ∀ t i, G.PortAt cap demand t.val (output t i))
    (hdet : ∀ t, ((G.linearCircuit cap demand).outputMatrix coeff (output t)).det ≠ 0) :
    ∃ c : G.Code N, (∀ i, c.messages i = 2 ^ (b * demand i)) ∧
      ∀ v hv m, c.decode v hv m = m := by
  classical
  let sym := inputSymbols hcard demand
  let packet : Message (fun i ↦ 2 ^ (b * demand i)) → (e : Fin edges) → G.Packet N e :=
    fun m e ↦ G.packedPacket hcard cap hbits e (fun j ↦ (G.linearCircuit cap demand).value coeff ⟨e, j⟩ (sym m))
  have hpacket (m m' : Message (fun i ↦ 2 ^ (b * demand i))) (e : Fin edges)
      (he : packet m e = packet m' e) (j : Fin (cap e)) :
      (G.linearCircuit cap demand).value coeff ⟨e, j⟩ (sym m) = (G.linearCircuit cap demand).value coeff ⟨e, j⟩ (sym m') :=
    congrFun (G.packedPacket_injective hcard cap hbits e he) j
  have hsym (m m' : Message (fun i ↦ 2 ^ (b * demand i))) (i : Fin sources)
      (hi : m i = m' i) (j : Fin (demand i)) : sym m ⟨i, j⟩ = sym m' ⟨i, j⟩ := by
    dsimp [sym, inputSymbols]
    rw [hi]
  have hpacket_local : ∀ e m m',
      (∀ i, G.sourceNode i = G.source e → m i = m' i) →
      (∀ a, G.target a = G.source e → packet m a = packet m' a) →
      packet m e = packet m' e := by
    intro e m m' hmsg hpkt
    apply congrArg (G.packedPacket hcard cap hbits e)
    funext j
    rw [(G.linearCircuit cap demand).value_eq, (G.linearCircuit cap demand).value_eq]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (G.linearCircuit cap demand).input ⟨e, j⟩ i
      · simp only [hi, ite_true]
        rw [hsym m m' i.1 (hmsg i.1 hi) i.2]
      · simp [hi]
    · apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (G.linearCircuit cap demand).parent ⟨e, j⟩ a
      · simp only [ha, ite_true]
        rw [hpacket m m' a.1 (hpkt a.1 ha) a.2]
      · simp [ha]
  have recover : ∀ v (hv : v ∈ G.sinks) m m',
      (∀ i, G.sourceNode i = v → m i = m' i) →
      (∀ a, G.target a = v → packet m a = packet m' a) → m = m' := by
    intro v hv m m' hmsg hpkt
    apply inputSymbols_injective hcard demand
    have hobs : (fun i ↦ (G.linearCircuit cap demand).portValue coeff (sym m) (output ⟨v, hv⟩ i)) =
        (fun i ↦ (G.linearCircuit cap demand).portValue coeff (sym m') (output ⟨v, hv⟩ i)) := by
      funext i
      have hi := hlocal ⟨v, hv⟩ i
      cases ho : output ⟨v, hv⟩ i with
      | inl a =>
        simp only [ho, PortAt] at hi
        exact hsym m m' a.1 (hmsg a.1 hi) a.2
      | inr e =>
        simp only [ho, PortAt] at hi
        exact hpacket m m' e.1 (hpkt e.1 hi) e.2
    have hdec := congrArg ((G.linearCircuit cap demand).decode coeff (output ⟨v, hv⟩)) hobs
    have hd : ((G.linearCircuit cap demand).outputMatrix coeff (output ⟨v, hv⟩)).det ≠ 0 := hdet ⟨v, hv⟩
    have hm := (G.linearCircuit cap demand).decode_eq (K := K) (c := coeff) (output := output ⟨v, hv⟩) (hd := hd) (m := sym m)
    have hm' := (G.linearCircuit cap demand).decode_eq (K := K) (c := coeff) (output := output ⟨v, hv⟩) (hd := hd) (m := sym m')
    exact hm.symm.trans (hdec.trans hm')
  -- Invertibility makes the identity on actual messages a local decoder;
  -- `exists_localDecode` extends it to every possible local observation.
  refine ⟨{
    messages := fun i ↦ 2 ^ (b * demand i)
    messages_pos := fun i ↦ Nat.two_pow_pos _
    packet := packet
    packet_local := hpacket_local
    decode := fun _ _ m ↦ m
    decode_local := recover
  }, fun _ ↦ rfl, fun _ _ _ ↦ rfl⟩

end CapacityAtlas.Multisource.Network
