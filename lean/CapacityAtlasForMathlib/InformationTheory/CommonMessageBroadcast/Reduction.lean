/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasCommonMessage/blob/83923a9a73280ff2d24c71411398438edcc20e4b/CapacityAtlasCommonMessage/Reduction.lean
-/

import CapacityAtlasForMathlib.InformationTheory.CommonMessageBroadcastInformation
import CapacityAtlasForMathlib.InformationTheory.OutputRelabeling

namespace CapacityAtlas.CommonMessageBroadcast

variable {J X : Type*} {Y : J → Type*}

/-- A receiver word is embedded as a word with a constant receiver tag. -/
def bundleTag {n : ℕ} (word : (j : J) × (Fin n → Y j)) : Fin n → Sigma Y :=
  fun i ↦ ⟨word.1, word.2 i⟩

theorem bundleTag_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (bundleTag (Y := Y) (n := n)) := by
  rintro ⟨j, ys⟩ ⟨k, zs⟩ h
  have hindex : j = k := congrArg Sigma.fst (congrFun h ⟨0, hn⟩)
  cases hindex
  congr 1
  funext i
  exact sigma_mk_injective (congrFun h i)

namespace BlockCode

variable {n : ℕ}

/-- A compound decoder can be used by each receiver after inserting its tag. -/
def fromCompound (code : CompoundChannel.BlockCode X (Sigma Y) n) : BlockCode X Y n where
  messageCount := code.messageCount
  messageCount_pos := code.messageCount_pos
  encode := code.encode
  decode j word := code.decode (bundleTag ⟨j, word⟩)

@[simp]
theorem rate_fromCompound (code : CompoundChannel.BlockCode X (Sigma Y) n) :
    (fromCompound code).rate = code.rate := rfl

/-- Extending the receiver decoders gives one decoder on the common tagged alphabet. -/
noncomputable def toCompound (code : BlockCode X Y n) :
    CompoundChannel.BlockCode X (Sigma Y) n where
  messageCount := code.messageCount
  messageCount_pos := code.messageCount_pos
  encode := code.encode
  decode := Function.extend bundleTag (fun word ↦ code.decode word.1 word.2)
    (fun _ ↦ ⟨0, code.messageCount_pos⟩)

@[simp]
theorem rate_toCompound (code : BlockCode X Y n) : code.toCompound.rate = code.rate := rfl

theorem toCompound_decode_bundleTag (code : BlockCode X Y n) (hn : 0 < n)
    (j : J) (word : Fin n → Y j) :
    code.toCompound.decode (bundleTag ⟨j, word⟩) = code.decode j word :=
  (bundleTag_injective hn).extend_apply (fun word ↦ code.decode word.1 word.2)
    (fun _ ↦ ⟨0, code.messageCount_pos⟩) ⟨j, word⟩

theorem fromCompound_toCompound (code : BlockCode X Y n) (hn : 0 < n) :
    fromCompound code.toCompound = code := by
  cases code with
  | mk messages hmessages encode decode =>
    dsimp [fromCompound, toCompound]
    congr 1
    funext j word
    exact (bundleTag_injective hn).extend_apply (fun word ↦ decode word.1 word.2)
      (fun _ ↦ ⟨0, hmessages⟩) ⟨j, word⟩

variable [Fintype J] [Fintype X] [∀ j, Fintype (Y j)]

/-- Inserting a receiver tag preserves that receiver's exact average error. -/
theorem averageErrorProbability_fromCompound
    (channels : (j : J) → FiniteChannel X (Y j))
    (code : CompoundChannel.BlockCode X (Sigma Y) n) (j : J) :
    (fromCompound code).averageErrorProbability channels j =
      code.averageErrorProbability (taggedChannels channels j) := by
  classical
  exact FiniteChannel.BlockCode.averageErrorProbability_pullbackOutput
    (channel := channels j) (f := Sigma.mk j) (code.onChannel (taggedChannels channels j))

/-- The extended decoder has the original error on every supported receiver alphabet. -/
theorem averageErrorProbability_toCompound
    (channels : (j : J) → FiniteChannel X (Y j)) (code : BlockCode X Y n)
    (hn : 0 < n) (j : J) :
    code.toCompound.averageErrorProbability (taggedChannels channels j) =
      code.averageErrorProbability channels j := by
  rw [← averageErrorProbability_fromCompound channels code.toCompound j,
    fromCompound_toCompound code hn]

end BlockCode

variable [Fintype J] [Fintype X] [∀ j, Fintype (Y j)]

/-- Tagged compound codes and heterogeneous receiver codes achieve exactly the same rates. -/
theorem achievableRate_iff_taggedChannels
    (channels : (j : J) → FiniteChannel X (Y j)) (rate : ℝ) :
    AchievableRate channels rate ↔ CompoundChannel.AchievableRate (taggedChannels channels) rate := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN, hcodes⟩ := h ε hε
    refine ⟨N, hN, ?_⟩
    intro n hn
    obtain ⟨code, herror, hrate⟩ := hcodes n hn
    refine ⟨code.toCompound, ?_, hrate⟩
    intro j
    rw [BlockCode.averageErrorProbability_toCompound channels code (hN.trans_le hn) j]
    exact herror j
  · intro h ε hε
    obtain ⟨N, hN, hcodes⟩ := h ε hε
    refine ⟨N, hN, ?_⟩
    intro n hn
    obtain ⟨code, herror, hrate⟩ := hcodes n hn
    refine ⟨BlockCode.fromCompound code, ?_, hrate⟩
    intro j
    rw [BlockCode.averageErrorProbability_fromCompound]
    exact herror j

/-- The two operational suprema agree without an auxiliary boundedness premise. -/
theorem operationalCapacityBits_eq_taggedChannels
    (channels : (j : J) → FiniteChannel X (Y j)) :
    operationalCapacityBits channels =
      CompoundChannel.operationalCapacityBits (taggedChannels channels) := by
  unfold operationalCapacityBits CompoundChannel.operationalCapacityBits
  congr 1
  ext rate
  simp only [Set.mem_setOf_eq, achievableRate_iff_taggedChannels]

end CapacityAtlas.CommonMessageBroadcast
