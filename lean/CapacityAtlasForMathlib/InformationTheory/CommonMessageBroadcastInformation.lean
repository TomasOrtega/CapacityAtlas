/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.CommonMessageBroadcast
import CapacityAtlasForMathlib.InformationTheory.CompoundChannel

open scoped BigOperators

namespace CapacityAtlas.CommonMessageBroadcast

variable {J X : Type*} {Y : J → Type*}
  [Fintype J] [Fintype X] [∀ j, Fintype (Y j)]

/-- A receiver tag places heterogeneous outputs in one common alphabet. -/
@[capacity_shared_api]
noncomputable def taggedChannels (channels : (j : J) → FiniteChannel X (Y j)) :
    J → FiniteChannel X (Sigma Y) := by
  classical
  exact fun j ↦ (channels j).relabelOutput (Sigma.mk j)

@[capacity_shared_api]
theorem taggedChannels_mutualInformation (channels : (j : J) → FiniteChannel X (Y j))
    (j : J) (input : FiniteDistribution X) :
    (taggedChannels channels j).mutualInformation input = (channels j).mutualInformation input := by
  classical
  exact (channels j).relabelOutput_mutualInformation (Sigma.mk j) sigma_mk_injective input

@[capacity_shared_api]
theorem taggedChannels_mutualInformationBits (channels : (j : J) → FiniteChannel X (Y j))
    (j : J) (input : FiniteDistribution X) :
    (taggedChannels channels j).mutualInformationBits input =
      (channels j).mutualInformationBits input := by
  unfold FiniteChannel.mutualInformationBits
  rw [taggedChannels_mutualInformation]

/-- The least information available to a receiver, in bits. -/
@[capacity_shared_api]
noncomputable def worstInformationBits [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) (input : FiniteDistribution X) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j ↦ (channels j).mutualInformationBits input)

@[capacity_shared_api]
theorem worstInformationBits_le [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) (input : FiniteDistribution X) (j : J) :
    worstInformationBits channels input ≤ (channels j).mutualInformationBits input :=
  Finset.inf'_le _ (Finset.mem_univ j)

@[capacity_shared_api]
theorem le_worstInformationBits [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) (input : FiniteDistribution X) {value : ℝ}
    (h : ∀ j, value ≤ (channels j).mutualInformationBits input) :
    value ≤ worstInformationBits channels input :=
  Finset.le_inf' Finset.univ_nonempty _ fun j _ ↦ h j

@[capacity_shared_api]
theorem worstInformationBits_taggedChannels [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) (input : FiniteDistribution X) :
    CompoundChannel.worstInformationBits (taggedChannels channels) input =
      worstInformationBits channels input := by
  simp only [CompoundChannel.worstInformationBits, worstInformationBits,
    taggedChannels_mutualInformationBits]

/-- The maximum of the least receiver information, expressed as a supremum. -/
@[capacity_shared_api]
noncomputable def informationCapacityBits [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) : ℝ :=
  sSup (Set.range (worstInformationBits channels))

@[capacity_shared_api]
theorem informationCapacityBits_taggedChannels [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) :
    CompoundChannel.informationCapacityBits (taggedChannels channels) =
      informationCapacityBits channels := by
  have hfun := funext (worstInformationBits_taggedChannels channels)
  unfold CompoundChannel.informationCapacityBits informationCapacityBits
  rw [hfun]

@[capacity_shared_api]
theorem worstInformationBits_bddAbove [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) :
    BddAbove (Set.range (worstInformationBits channels)) := by
  have hfun := funext (worstInformationBits_taggedChannels channels)
  rw [← hfun]
  exact CompoundChannel.worstInformationBits_bddAbove (taggedChannels channels)

@[capacity_shared_api]
theorem worstInformationBits_nonnegative [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) (input : FiniteDistribution X) :
    0 ≤ worstInformationBits channels input := by
  rw [← worstInformationBits_taggedChannels]
  exact CompoundChannel.worstInformationBits_nonnegative (taggedChannels channels) input

@[capacity_shared_api]
theorem worstInformationBits_le_informationCapacityBits [Nonempty J]
    (channels : (j : J) → FiniteChannel X (Y j)) (input : FiniteDistribution X) :
    worstInformationBits channels input ≤ informationCapacityBits channels :=
  le_csSup (worstInformationBits_bddAbove channels) (Set.mem_range_self input)

@[capacity_shared_api]
theorem informationCapacityBits_nonnegative [Nonempty J] [Nonempty X]
    (channels : (j : J) → FiniteChannel X (Y j)) : 0 ≤ informationCapacityBits channels := by
  rw [← informationCapacityBits_taggedChannels]
  exact CompoundChannel.informationCapacityBits_nonnegative (taggedChannels channels)

/-- Some common input law attains the maximum of the least receiver information. -/
@[capacity_shared_api]
theorem exists_capacityAchieving_input [Nonempty J] [Nonempty X]
    (channels : (j : J) → FiniteChannel X (Y j)) :
    ∃ input : FiniteDistribution X,
      worstInformationBits channels input = informationCapacityBits channels := by
  obtain ⟨input, hinput⟩ := CompoundChannel.exists_capacityAchieving_input (taggedChannels channels)
  exact ⟨input, by simpa only [worstInformationBits_taggedChannels,
    informationCapacityBits_taggedChannels] using hinput⟩

end CapacityAtlas.CommonMessageBroadcast
