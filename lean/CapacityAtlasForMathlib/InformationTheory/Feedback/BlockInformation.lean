/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasFeedback/blob/b35299f221ad1c17ccbafb45082c22a5379a99e9/CapacityAtlasFeedback/BlockInformation.lean
Adapted imports and reused shared output relabeling and information bounds.
-/

import CapacityAtlasForMathlib.InformationTheory.Feedback
import CapacityAtlasForMathlib.InformationTheory.SequentialInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasFeedback

attribute [local instance] Classical.propDecidable

variable {X Y M : Type*} [Fintype X] [Fintype Y] [Fintype M]

/-- Append the final symbol to the preceding output word. -/
def snocOutput (Y : Type*) (n : ℕ) : ((Fin n → Y) × Y) ≃ (Fin (n + 1) → Y) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ ↦ Y)

omit [Fintype Y] in
@[simp]
theorem snocOutput_apply (n : ℕ) (outputs : Fin n → Y) (output : Y) :
    snocOutput Y n (outputs, output) = Fin.snoc outputs output := rfl

/-- The adaptive block law is a sequential extension of its first `n` uses. -/
theorem sequentialExtension_relabel_eq_block (channel : FiniteChannel X Y) (n : ℕ)
    (encode : M → Feedback.Policy X Y (n + 1)) :
    (FiniteChannel.sequentialExtension
      ((Feedback.blockChannel channel n).encoded (fun m ↦ (encode m).init))
      channel (fun m history ↦ encode m (Fin.last n) history)).relabelOutput
        (snocOutput Y n) =
      (Feedback.blockChannel channel (n + 1)).encoded encode := by
  classical
  apply (FiniteChannel.relabelOutput_eq_iff _ (snocOutput Y n) _).mpr
  rintro m ⟨history, last⟩
  change (Feedback.blockChannel channel n).transition (encode m).init history *
      channel.transition (encode m (Fin.last n) history) last =
    (Feedback.blockChannel channel (n + 1)).transition (encode m) (Fin.snoc history last)
  exact (Feedback.blockChannel_transition_snoc channel (encode m) history last).symm

/-- Adaptively selected inputs obey the ordinary channel's block information bound. -/
theorem block_mutualInformation_le (channel : FiniteChannel X Y) (n : ℕ)
    (encode : M → Feedback.Policy X Y n) (input : FiniteDistribution M) :
    ((Feedback.blockChannel channel n).encoded encode).mutualInformation input ≤
      (n : ℝ) * channel.informationCapacityBits * Real.log 2 := by
  classical
  induction n with
  | zero =>
      simp only [FiniteChannel.mutualInformation, FiniteChannel.conditionalOutputEntropy,
        FiniteDistribution.entropy_of_subsingleton, mul_zero, Finset.sum_const_zero,
        sub_self, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
      let past := (Feedback.blockChannel channel n).encoded (fun m ↦ (encode m).init)
      let strategy := fun m history ↦ encode m (Fin.last n) history
      let extended := FiniteChannel.sequentialExtension past channel strategy
      have heq : extended.relabelOutput (snocOutput Y n) =
          (Feedback.blockChannel channel (n + 1)).encoded encode :=
        sequentialExtension_relabel_eq_block channel n encode
      have hinfo :
          ((Feedback.blockChannel channel (n + 1)).encoded encode).mutualInformation input =
            extended.mutualInformation input := by
        rw [← heq]
        exact extended.relabelOutput_mutualInformation (snocOutput Y n)
          (snocOutput Y n).injective input
      have hstep := FiniteChannel.sequentialExtension_mutualInformation_le_add_capacity
        past channel strategy input
      have hprevious := ih (fun m ↦ (encode m).init)
      rw [hinfo]
      change extended.mutualInformation input ≤
        past.mutualInformation input + channel.informationCapacityBits * Real.log 2 at hstep
      change past.mutualInformation input ≤ _ at hprevious
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith

end CapacityAtlasFeedback
