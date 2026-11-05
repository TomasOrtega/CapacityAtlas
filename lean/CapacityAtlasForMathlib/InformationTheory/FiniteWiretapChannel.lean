/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity

namespace CapacityAtlas

/-- Two finite DMCs with a common input, one legitimate and one eavesdropping. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure FiniteWiretapChannel (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z] where
  /-- Marginal channel observed by the intended receiver. -/
  legitimate : FiniteChannel X Y
  /-- Marginal channel observed by the eavesdropper. -/
  eavesdropper : FiniteChannel X Z

/-- A stochastic wiretap block code; `randomizationCount` is private encoder randomness. -/
@[capacity_problem "general-finite-wiretap-channel", capacity_definition]
structure WiretapCode {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (channel : FiniteWiretapChannel X Y Z) (blocklength : ℕ) where
  /-- Number of distinct messages. -/
  messageCount : ℕ
  /-- The message set is nonempty. -/
  messageCount_pos : 0 < messageCount
  /-- Number of private encoder-randomization indices. -/
  randomizationCount : ℕ
  /-- The private randomization set is nonempty. -/
  randomizationCount_pos : 0 < randomizationCount
  /-- Input word selected by the message and private randomization index. -/
  encode : Fin messageCount → Fin randomizationCount → Fin blocklength → X
  /-- Message estimate obtained from the output word. -/
  decode : (Fin blocklength → Y) → Fin messageCount

/-- A finite auxiliary `V`, its law, and a stochastic prefixing channel `V → X`. -/
structure WiretapAuxiliary (X : Type*) [Fintype X] where
  /-- Type of auxiliary symbols. -/
  Carrier : Type
  /-- Finite enumeration of the auxiliary alphabet. -/
  fintype : Fintype Carrier
  /-- Decidable equality for auxiliary symbols. -/
  decidableEq : DecidableEq Carrier
  /-- Probability law of the auxiliary symbol. -/
  distribution : @FiniteDistribution Carrier fintype
  /-- Stochastic prefixing channel from the auxiliary alphabet to physical inputs. -/
  encoder : @FiniteChannel Carrier X fintype inferInstance

/-- Legitimate-minus-eavesdropper auxiliary mutual information through prefixing, in bits. -/
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
