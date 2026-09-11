/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.DecoderSideInformation
import CapacityAtlasForMathlib.InformationTheory.FiniteChannelOptimization
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators

namespace CapacityAtlas.Channel

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- The receiver observes state and output; the encoder supplies an input without observing state. -/
@[capacity_problem "finite-dmc-decoder-state", capacity_definition]
def decoderStateChannel (state : FiniteDistribution S) (channels : S → FiniteChannel X Y) :
    FiniteChannel X (S × Y) :=
  FiniteChannel.withDecoderState state channels

/-- The input law is shared across states because the encoder does not know the state. -/
@[capacity_problem "finite-dmc-decoder-state", capacity_definition]
noncomputable def decoderStateInformationCapacityBits
    (state : FiniteDistribution S) (channels : S → FiniteChannel X Y) : ℝ :=
  sSup (Set.range fun input : FiniteDistribution X ↦
    ∑ s, state s * (channels s).mutualInformationBits input)

/-- The operational capacity equals the conditional-information supremum. -/
@[capacity_problem "finite-dmc-decoder-state", capacity_statement, capacity_solved,
  capacity_formal_proof, capacity_claim "exact-capacity" 1]
theorem decoderState_operationalCapacity [Nonempty X]
    (state : FiniteDistribution S) (channels : S → FiniteChannel X Y) :
    (decoderStateChannel state channels).operationalCapacityBits =
      decoderStateInformationCapacityBits state channels := by
  rw [FiniteChannel.codingTheorem]
  exact congrArg (fun f : FiniteDistribution X → ℝ ↦ sSup (Set.range f))
    (funext (FiniteChannel.withDecoderState_mutualInformationBits state channels))

/-- Compactness provides a capacity-achieving input independent of the state. -/
@[capacity_problem "finite-dmc-decoder-state", capacity_statement, capacity_solved,
  capacity_formal_proof, capacity_claim "optimizing-input" 1]
theorem decoderState_capacityAchieving_input [Nonempty X]
    (state : FiniteDistribution S) (channels : S → FiniteChannel X Y) :
    ∃ input : FiniteDistribution X,
      (∑ s, state s * (channels s).mutualInformationBits input) =
        (decoderStateChannel state channels).operationalCapacityBits := by
  obtain ⟨input, hinput⟩ := (decoderStateChannel state channels).exists_capacityAchieving_input
  refine ⟨input, ?_⟩
  rw [FiniteChannel.codingTheorem]
  simpa only [decoderStateChannel, FiniteChannel.withDecoderState_mutualInformationBits] using hinput

end CapacityAtlas.Channel
