/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteBroadcastChannel
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- A private stochastic encoder sends a common message and an independent secret message. -/
@[capacity_problem "broadcast-channel-confidential-messages", capacity_definition]
structure Code (W : FiniteBroadcastChannel X Y Z) (n : ℕ) where
  commonCount : ℕ
  secretCount : ℕ
  commonCount_pos : 0 < commonCount
  secretCount_pos : 0 < secretCount
  encode : FiniteChannel (Fin commonCount × Fin secretCount) (Fin n → X)
  decodeLegitimate : (Fin n → Y) → Fin commonCount × Fin secretCount
  decodeCommon : (Fin n → Z) → Fin commonCount

namespace Code

variable {W : FiniteBroadcastChannel X Y Z} {n : ℕ}

noncomputable def messages (c : Code W n) : FiniteDistribution (Fin c.commonCount × Fin c.secretCount) := by
  letI : Nonempty (Fin c.commonCount) := Fin.pos_iff_nonempty.mp c.commonCount_pos
  letI : Nonempty (Fin c.secretCount) := Fin.pos_iff_nonempty.mp c.secretCount_pos
  exact FiniteDistribution.uniform _

def induced (c : Code W n) {O : Type*} [Fintype O] (V : FiniteChannel X O) :
    FiniteChannel (Fin c.commonCount × Fin c.secretCount) (Fin n → O) :=
  (V.block n).comp c.encode

noncomputable def joint (c : Code W n) {O : Type*} [Fintype O] (V : FiniteChannel X O) :=
  FiniteInformation.joint c.messages (c.induced V)

noncomputable def legitimateError (c : Code W n) : ℝ := by
  classical
  exact ∑ a, ∑ y, if c.decodeLegitimate y = a then 0
    else c.messages a * (c.induced W.receiver₁).transition a y

noncomputable def commonError (c : Code W n) : ℝ := by
  classical
  exact ∑ a, ∑ z, if c.decodeCommon z = a.1 then 0
    else c.messages a * (c.induced W.receiver₂).transition a z

noncomputable def error (c : Code W n) : ℝ := max c.legitimateError c.commonError

/-- Weak secrecy uses leakage per physical channel use. -/
noncomputable def leakage (c : Code W n) : ℝ :=
  FiniteInformation.information (c.joint W.receiver₂) (fun a ↦ a.1.2) Prod.snd / n

noncomputable def defect (c : Code W n) : ℝ := max c.error c.leakage

noncomputable def rates (c : Code W n) : RatePair :=
  (Operational.messageRate c.commonCount n, Operational.messageRate c.secretCount n)

end Code

/-- Closure in rate is built into the simultaneous reliability and weak-secrecy criterion. -/
@[capacity_problem "broadcast-channel-confidential-messages", capacity_definition]
def capacityRegion (W : FiniteBroadcastChannel X Y Z) : Set RatePair :=
  Operational.achievableRegion (Code W) (fun _ _ ↦ True)
    (fun _ c ↦ c.defect) (fun _ c ↦ c.rates)

def auxiliaryJoint {U V : Type*} [Fintype U] [Fintype V]
    (p : FiniteDistribution (U × V))
    (prefixing : FiniteChannel V X) {O : Type*} [Fintype O]
    (W : FiniteChannel X O) : FiniteDistribution ((U × V) × O) :=
  FiniteInformation.joint p ((W.comp prefixing).encoded Prod.snd)

/-- The factorization through `prefixing` enforces the chain U → V → X → (Y,Z). -/
def auxiliaryRegion (W : FiniteBroadcastChannel X Y Z) : Set RatePair :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ u v : ℕ, ∃ p : FiniteDistribution (Fin u × Fin v),
      ∃ prefixing : FiniteChannel (Fin v) X,
      let py := auxiliaryJoint p prefixing W.receiver₁
      let pz := auxiliaryJoint p prefixing W.receiver₂
      r.1 ≤ FiniteInformation.information py (fun a ↦ a.1.1) Prod.snd ∧
      r.1 ≤ FiniteInformation.information pz (fun a ↦ a.1.1) Prod.snd ∧
      r.2 ≤ FiniteInformation.conditional py (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1) -
        FiniteInformation.conditional pz (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1)}

@[capacity_problem "broadcast-channel-confidential-messages", capacity_definition]
def informationRegion (W : FiniteBroadcastChannel X Y Z) : Set RatePair :=
  closure (auxiliaryRegion W)

end CapacityAtlas.ConfidentialBroadcast
