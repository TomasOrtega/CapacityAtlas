/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalTheory

namespace CapacityAtlas

/-- Two finite DMCs with a common input, one legitimate and one eavesdropping. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure FiniteWiretapChannel (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z] where
  legitimate : FiniteChannel X Y
  eavesdropper : FiniteChannel X Z

/-- A stochastic wiretap block code; `randomizationCount` is private encoder randomness. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure WiretapCode {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (channel : FiniteWiretapChannel X Y Z) (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  randomizationCount : ℕ
  randomizationCount_pos : 0 < randomizationCount
  encode : Fin messageCount → Fin randomizationCount → Fin blocklength → X
  decode : (Fin blocklength → Y) → Fin messageCount

/-- Strong and weak secrecy are deliberately different operational predicates. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure WiretapOperationalTheory (Model : Type*) where
  strongSecrecyAchievable : Model → ℝ → Prop
  weakSecrecyAchievable : Model → ℝ → Prop

namespace WiretapOperationalTheory

noncomputable def strongCapacity {Model : Type*} (theory : WiretapOperationalTheory Model)
    (model : Model) : ℝ :=
  sSup {rate | theory.strongSecrecyAchievable model rate}

noncomputable def weakCapacity {Model : Type*} (theory : WiretapOperationalTheory Model)
    (model : Model) : ℝ :=
  sSup {rate | theory.weakSecrecyAchievable model rate}

end WiretapOperationalTheory

/-- A finite auxiliary `V`, its law, and a stochastic prefixing channel `V → X`. -/
structure WiretapAuxiliary (X : Type*) [Fintype X] where
  Carrier : Type
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier
  distribution : @FiniteDistribution Carrier fintype
  encoder : @FiniteChannel Carrier X fintype inferInstance

noncomputable def wiretapAuxiliaryInformation {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (channel : FiniteWiretapChannel X Y Z) (auxiliary : WiretapAuxiliary X) : ℝ := by
  letI := auxiliary.fintype
  letI := auxiliary.decidableEq
  exact (channel.legitimate.comp auxiliary.encoder).mutualInformationBits
      auxiliary.distribution -
    (channel.eavesdropper.comp auxiliary.encoder).mutualInformationBits
      auxiliary.distribution

/-- The standard single-auxiliary value for an unconstrained finite wiretap channel. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
noncomputable def finiteWiretapAuxiliaryCapacity {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (channel : FiniteWiretapChannel X Y Z) : ℝ :=
  sSup (Set.range (wiretapAuxiliaryInformation channel))

end CapacityAtlas
