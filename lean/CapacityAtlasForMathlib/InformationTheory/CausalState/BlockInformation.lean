/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasCausalState/blob/0176a0e9fed6ec13fd2f566d9906c3ea8103d1cc/CapacityAtlasCausal/BlockInformation.lean
Adapted imports and reused shared output relabeling and information bounds.
-/

import CapacityAtlasForMathlib.InformationTheory.CausalState.BlockLaw
import CapacityAtlasForMathlib.InformationTheory.SequentialInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasCausal

attribute [local instance] Classical.propDecidable

variable {S X Y M : Type*} [Fintype S] [Fintype X] [Fintype Y] [Fintype M]

/-- Append the final symbol to the preceding output word. -/
def snocOutput (Y : Type*) (n : ℕ) : ((Fin n → Y) × Y) ≃ (Fin (n + 1) → Y) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ ↦ Y)

omit [Fintype Y] in
@[simp]
theorem snocOutput_apply (n : ℕ) (outputs : Fin n → Y) (output : Y) :
    snocOutput Y n (outputs, output) = Fin.snoc outputs output := rfl

theorem latentPast_eq_block (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ)
    (encode : M → CausalState.Policy S X (n + 1)) :
    FiniteChannel.latentPast (historyDistribution state n)
        (fun m ↦ conditionalOutput channels (encode m).init) =
      (CausalState.blockChannel state channels n).encoded (fun m ↦ (encode m).init) := by
  rfl

theorem latentExtension_relabel_eq_block (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ)
    (encode : M → CausalState.Policy S X (n + 1)) :
    (FiniteChannel.latentExtension (historyDistribution state n)
      (fun m ↦ conditionalOutput channels (encode m).init)
      (CausalState.strategyChannel state channels)
      (fun m ↦ lastStrategy (encode m))).relabelOutput (snocOutput Y n) =
        (CausalState.blockChannel state channels (n + 1)).encoded encode := by
  classical
  apply (FiniteChannel.relabelOutput_eq_iff _ (snocOutput Y n) _).mpr
  rintro m ⟨past, last⟩
  change (∑ history : Fin n → S, historyDistribution state n history *
      (conditionalOutput channels (encode m).init history past *
        (CausalState.strategyChannel state channels).transition
          (lastStrategy (encode m) history) last)) =
    (CausalState.blockChannel state channels (n + 1)).transition (encode m) (Fin.snoc past last)
  rw [blockChannel_transition_snoc]
  apply Finset.sum_congr rfl
  intro history _
  ring

/-- Every causal encoder family obeys the strategy-channel block information bound. -/
theorem block_mutualInformation_le [Nonempty X] (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ)
    (encode : M → CausalState.Policy S X n) (input : FiniteDistribution M) :
    ((CausalState.blockChannel state channels n).encoded encode).mutualInformation input ≤
      (n : ℝ) * (CausalState.strategyChannel state channels).informationCapacityBits * Real.log 2 := by
  classical
  induction n with
  | zero =>
      simp only [FiniteChannel.mutualInformation, FiniteChannel.conditionalOutputEntropy,
        FiniteDistribution.entropy_of_subsingleton, mul_zero, Finset.sum_const_zero,
        sub_self, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
      let next := CausalState.strategyChannel state channels
      let past := fun m ↦ conditionalOutput channels (encode m).init
      let strategy := fun m ↦ lastStrategy (encode m)
      let extended := FiniteChannel.latentExtension (historyDistribution state n) past next strategy
      have heq : extended.relabelOutput (snocOutput Y n) =
          (CausalState.blockChannel state channels (n + 1)).encoded encode :=
        latentExtension_relabel_eq_block state channels n encode
      have hinfo :
          ((CausalState.blockChannel state channels (n + 1)).encoded encode).mutualInformation input =
            extended.mutualInformation input := by
        rw [← heq]
        exact extended.relabelOutput_mutualInformation (snocOutput Y n)
          (snocOutput Y n).injective input
      have hstep := FiniteChannel.latentExtension_mutualInformation_le_add_capacity
        (historyDistribution state n) past next strategy input
      have hpast : FiniteChannel.latentPast (historyDistribution state n) past =
          (CausalState.blockChannel state channels n).encoded (fun m ↦ (encode m).init) :=
        latentPast_eq_block state channels n encode
      rw [hpast] at hstep
      have hprevious := ih (fun m ↦ (encode m).init)
      rw [hinfo]
      change extended.mutualInformation input ≤ _ at hstep
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith

end CapacityAtlasCausal
