/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteWiretapChannel
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.FiniteMixture
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion

open scoped BigOperators

namespace CapacityAtlas.WiretapOperational

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The actual message-to-observation channel, averaging the finite private seed. -/
noncomputable def induced {W : FiniteWiretapChannel X Y Z} {n : ℕ}
    (c : WiretapCode W n) {O : Type*} [Fintype O] (V : FiniteChannel X O) :
    FiniteChannel (Fin c.messageCount) (Fin n → O) := by
  letI : Nonempty (Fin c.randomizationCount) := Fin.pos_iff_nonempty.mp c.randomizationCount_pos
  exact FiniteChannel.ofRows fun m ↦
    (FiniteDistribution.uniform (Fin c.randomizationCount)).mixture
      (fun seed ↦ (V.block n).rowDistribution (c.encode m seed))

noncomputable def error {W : FiniteWiretapChannel X Y Z} {n : ℕ}
    (c : WiretapCode W n) : ℝ :=
  FiniteInformation.decodingError (induced c W.legitimate) c.messageCount id c.decode

/-- Unnormalized leakage in bits. There is deliberately no division by blocklength. -/
noncomputable def leakage {W : FiniteWiretapChannel X Y Z} {n : ℕ}
    (c : WiretapCode W n) : ℝ := by
  letI : Nonempty (Fin c.messageCount) := Fin.pos_iff_nonempty.mp c.messageCount_pos
  exact (induced c W.eavesdropper).mutualInformationBits
    (FiniteDistribution.uniform (Fin c.messageCount))

/-- Both reliability and strong secrecy must vanish. -/
noncomputable def defect {W : FiniteWiretapChannel X Y Z} {n : ℕ}
    (c : WiretapCode W n) : ℝ := max (error c) (leakage c)

noncomputable def rate {W : FiniteWiretapChannel X Y Z} {n : ℕ}
    (c : WiretapCode W n) := Operational.messageRate c.messageCount n

noncomputable def capacity (W : FiniteWiretapChannel X Y Z) : ℝ :=
  Operational.capacity (WiretapCode W) (fun _ _ ↦ True)
    (fun _ c ↦ defect c) (fun _ c ↦ rate c)

def IsDegraded (W : FiniteWiretapChannel X Y Z) : Prop :=
  ∃ degrade : FiniteChannel Y Z, W.eavesdropper = degrade.comp W.legitimate

noncomputable def degradedInformationCapacity (W : FiniteWiretapChannel X Y Z) : ℝ :=
  sSup (Set.range fun p : FiniteDistribution X ↦
    W.legitimate.mutualInformationBits p - W.eavesdropper.mutualInformationBits p)

end CapacityAtlas.WiretapOperational
