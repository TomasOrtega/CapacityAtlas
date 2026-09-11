/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteEntropy
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

open scoped BigOperators

namespace CapacityAtlas.CompoundChannel

/-- One encoder and one decoder, independent of the unknown channel member. -/
@[capacity_shared_api]
structure BlockCode (X Y : Type*) (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  encode : Fin messageCount → Fin blocklength → X
  decode : (Fin blocklength → Y) → Fin messageCount

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

namespace BlockCode

variable {n : ℕ}

/-- Interpret the same maps on any fixed memoryless channel. -/
@[capacity_shared_api]
def onChannel (code : BlockCode X Y n) (channel : FiniteChannel X Y) :
    FiniteChannel.BlockCode channel n where
  messageCount := code.messageCount
  messageCount_pos := code.messageCount_pos
  encode := code.encode
  decode := code.decode

/-- Rate in bits per channel use. -/
@[capacity_shared_api]
noncomputable def rate (code : BlockCode X Y n) : ℝ :=
  Real.logb 2 code.messageCount / n

/-- Average error for a fixed member under uniform messages. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability (code : BlockCode X Y n)
    (channel : FiniteChannel X Y) : ℝ :=
  (code.onChannel channel).averageErrorProbability

@[simp, capacity_shared_api]
theorem onChannel_rate (code : BlockCode X Y n) (channel : FiniteChannel X Y) :
    (code.onChannel channel).rate = code.rate := rfl

@[simp, capacity_shared_api]
theorem onChannel_messageCount (code : BlockCode X Y n) (channel : FiniteChannel X Y) :
    (code.onChannel channel).messageCount = code.messageCount := rfl

end BlockCode

/-- Uniform reliability for every fixed channel member, at all sufficiently large lengths. -/
@[capacity_shared_api]
def AchievableRate (channels : S → FiniteChannel X Y) (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ firstBlocklength : ℕ, 0 < firstBlocklength ∧
    ∀ blocklength, firstBlocklength ≤ blocklength →
      ∃ code : BlockCode X Y blocklength,
        (∀ s, code.averageErrorProbability (channels s) ≤ ε) ∧ rate ≤ code.rate

omit [Fintype S] in
/-- A constant one-message code makes every nonpositive rate uniformly achievable. -/
@[capacity_shared_api]
theorem achievableRate_of_nonpos [Nonempty X]
    (channels : S → FiniteChannel X Y) {rate : ℝ} (hrate : rate ≤ 0) :
    AchievableRate channels rate := by
  classical
  intro ε hε
  refine ⟨1, by omega, ?_⟩
  intro n _
  let code : BlockCode X Y n :=
    { messageCount := 1
      messageCount_pos := by omega
      encode _ _ := Classical.choice inferInstance
      decode _ := 0 }
  refine ⟨code, ?_, ?_⟩
  · intro s
    have hzero : code.averageErrorProbability (channels s) = 0 := by
      change (FiniteChannel.BlockCode.oneMessage (channels s) n).averageErrorProbability = 0
      exact FiniteChannel.BlockCode.oneMessage_averageErrorProbability (channels s) n
    exact hzero.le.trans hε.le
  · simpa [BlockCode.rate, code] using hrate

/-- Compound capacity in bits per channel use, with zero included in the rate set. -/
@[capacity_shared_api]
noncomputable def operationalCapacityBits (channels : S → FiniteChannel X Y) : ℝ :=
  sSup {rate | rate = 0 ∨ AchievableRate channels rate}

/-- The least mutual information across a finite nonempty channel family. -/
@[capacity_shared_api]
noncomputable def worstInformationBits [Nonempty S]
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun s ↦ (channels s).mutualInformationBits input)

@[capacity_shared_api]
theorem worstInformationBits_le [Nonempty S]
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) (s : S) :
    worstInformationBits channels input ≤ (channels s).mutualInformationBits input :=
  Finset.inf'_le _ (Finset.mem_univ s)

@[capacity_shared_api]
theorem le_worstInformationBits [Nonempty S]
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) {value : ℝ}
    (h : ∀ s, value ≤ (channels s).mutualInformationBits input) :
    value ≤ worstInformationBits channels input :=
  Finset.le_inf' Finset.univ_nonempty _ fun s _ ↦ h s

@[capacity_shared_api]
theorem worstInformationBits_nonnegative [Nonempty S]
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) :
    0 ≤ worstInformationBits channels input := by
  apply le_worstInformationBits
  intro s
  exact div_nonneg ((channels s).mutualInformation_nonnegative input)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The max–min information target, expressed as a supremum over input distributions. -/
@[capacity_shared_api]
noncomputable def informationCapacityBits [Nonempty S]
    (channels : S → FiniteChannel X Y) : ℝ :=
  sSup (Set.range (worstInformationBits channels))

@[capacity_shared_api]
theorem worstInformationBits_bddAbove [Nonempty S]
    (channels : S → FiniteChannel X Y) :
    BddAbove (Set.range (worstInformationBits channels)) := by
  classical
  let s : S := Classical.choice inferInstance
  refine ⟨(channels s).informationCapacityBits, ?_⟩
  rintro value ⟨input, rfl⟩
  exact (worstInformationBits_le channels input s).trans
    ((channels s).mutualInformationBits_le_informationCapacityBits input)

@[capacity_shared_api]
theorem worstInformationBits_le_informationCapacityBits [Nonempty S]
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) :
    worstInformationBits channels input ≤ informationCapacityBits channels :=
  le_csSup (worstInformationBits_bddAbove channels) (Set.mem_range_self input)

@[capacity_shared_api]
theorem informationCapacityBits_nonnegative [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) : 0 ≤ informationCapacityBits channels :=
  (worstInformationBits_nonnegative channels (FiniteDistribution.uniform X)).trans
    (worstInformationBits_le_informationCapacityBits channels (FiniteDistribution.uniform X))

/-- A finite compound family admits an input attaining its max–min information target. -/
@[capacity_shared_api]
theorem exists_capacityAchieving_input [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) :
    ∃ input : FiniteDistribution X,
      worstInformationBits channels input = informationCapacityBits channels := by
  classical
  have hnonempty : (stdSimplex ℝ X).Nonempty := by
    let input := FiniteDistribution.uniform X
    exact ⟨input, input.nonnegative, input.sum_probability⟩
  let information : S → (X → ℝ) → ℝ := fun s p ↦
    ((∑ y, Real.negMulLog (∑ x, p x * (channels s).transition x y)) -
      ∑ x, p x * ((channels s).rowDistribution x).entropy) / Real.log 2
  let worst : (X → ℝ) → ℝ := fun p ↦
    Finset.univ.inf' Finset.univ_nonempty (fun s ↦ information s p)
  have hcontinuous : Continuous worst := by
    apply Continuous.finset_inf'_apply
    intro s _
    dsimp [information]
    fun_prop
  obtain ⟨p, hp, hmax⟩ :=
    (isCompact_stdSimplex ℝ X).exists_isMaxOn hnonempty hcontinuous.continuousOn
  let input : FiniteDistribution X := ⟨p, hp.1, hp.2⟩
  refine ⟨input, (IsGreatest.csSup_eq ?_).symm⟩
  refine ⟨Set.mem_range_self input, ?_⟩
  rintro value ⟨other, rfl⟩
  exact hmax ⟨other.nonnegative, other.sum_probability⟩

end CapacityAtlas.CompoundChannel
