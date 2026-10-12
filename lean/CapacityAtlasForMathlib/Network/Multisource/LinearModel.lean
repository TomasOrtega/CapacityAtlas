/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.Basic
import CapacityAtlasForMathlib.Network.LinearMulticast.Circuit

namespace CapacityAtlas.Multisource.Network

variable {vertices edges sources : ℕ} (G : Network vertices edges sources)

abbrev Input (demand : Fin sources → ℕ) := Σ i : Fin sources, Fin (demand i)
abbrev Wire (cap : Fin edges → ℕ) := Σ e : Fin edges, Fin (cap e)

noncomputable instance inputDecidableEq (demand : Fin sources → ℕ) :
    DecidableEq (Input demand) := Classical.decEq _

/-- One circuit wire per unit edge capacity and one scalar per source demand. -/
def linearCircuit (cap : Fin edges → ℕ) (demand : Fin sources → ℕ) :
    LinearMulticast.Circuit (Input demand) (Wire cap) where
  height e := (G.source e.1).val
  input e i := G.sourceNode i.1 = G.source e.1
  parent e p := G.target p.1 = G.source e.1
  parent_lt e p h := by simpa [← h] using G.increasing p.1

def PortAt (cap : Fin edges → ℕ) (demand : Fin sources → ℕ)
    (v : Fin vertices) : Input demand ⊕ Wire cap → Prop
  | Sum.inl i => G.sourceNode i.1 = v
  | Sum.inr e => G.target e.1 = v

end CapacityAtlas.Multisource.Network
