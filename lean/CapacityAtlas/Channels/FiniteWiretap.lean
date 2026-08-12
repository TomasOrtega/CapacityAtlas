/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteWiretapChannel

namespace CapacityAtlas.Channel

open CapacityAtlas

/-- Strong-secrecy capacity equals the single-auxiliary wiretap formula. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_statement]
def generalFiniteWiretapCapacityStatement {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (theory : WiretapOperationalTheory (FiniteWiretapChannel X Y Z))
    (channel : FiniteWiretapChannel X Y Z) : Prop :=
  theory.strongCapacity channel = finiteWiretapAuxiliaryCapacity channel

/-- Strong and weak secrecy have the same capacity, without identifying their criteria. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_statement]
def generalFiniteWiretapStrongWeakAgreement {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (theory : WiretapOperationalTheory (FiniteWiretapChannel X Y Z))
    (channel : FiniteWiretapChannel X Y Z) : Prop :=
  theory.strongCapacity channel = theory.weakCapacity channel

end CapacityAtlas.Channel
