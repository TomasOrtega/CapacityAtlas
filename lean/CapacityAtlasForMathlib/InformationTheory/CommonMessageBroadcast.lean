/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import CapacityAtlasForMathlib.InformationTheory.SequentialInformation

namespace CapacityAtlas.CommonMessageBroadcast

/-- One message encoder and a decoder for each receiver's own output alphabet. -/
@[capacity_shared_api]
structure BlockCode {J : Type*} (X : Type*) (Y : J → Type*) (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  encode : Fin messageCount → Fin blocklength → X
  decode : (j : J) → (Fin blocklength → Y j) → Fin messageCount

variable {J X : Type*} {Y : J → Type*}

namespace BlockCode

variable {n : ℕ}

@[capacity_shared_api]
instance (code : BlockCode X Y n) : Nonempty (Fin code.messageCount) :=
  Fin.pos_iff_nonempty.mp code.messageCount_pos

/-- Rate in bits per channel use. -/
@[capacity_shared_api]
noncomputable def rate (code : BlockCode X Y n) : ℝ :=
  Real.logb 2 code.messageCount / n

/-- A constant word carrying one message, recovered by every receiver. -/
@[capacity_shared_api]
noncomputable def oneMessage [Nonempty X] (n : ℕ) : BlockCode X Y n where
  messageCount := 1
  messageCount_pos := by omega
  encode _ _ := Classical.choice inferInstance
  decode _ _ := 0

@[simp, capacity_shared_api]
theorem oneMessage_messageCount [Nonempty X] (n : ℕ) :
    (oneMessage (X := X) (Y := Y) n).messageCount = 1 := rfl

@[simp, capacity_shared_api]
theorem oneMessage_rate [Nonempty X] (n : ℕ) :
    (oneMessage (X := X) (Y := Y) n).rate = 0 := by
  simp [rate]

variable [Fintype X] [∀ j, Fintype (Y j)]

/-- View the common encoder and one receiver's decoder as an ordinary block code. -/
@[capacity_shared_api]
def onReceiver (code : BlockCode X Y n) (channels : (j : J) → FiniteChannel X (Y j))
    (j : J) : FiniteChannel.BlockCode (channels j) n where
  messageCount := code.messageCount
  messageCount_pos := code.messageCount_pos
  encode := code.encode
  decode := code.decode j

/-- Receiver error averaged over the same uniform message at every receiver. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability (code : BlockCode X Y n)
    (channels : (j : J) → FiniteChannel X (Y j)) (j : J) : ℝ :=
  (code.onReceiver channels j).averageErrorProbability

@[simp, capacity_shared_api]
theorem onReceiver_rate (code : BlockCode X Y n)
    (channels : (j : J) → FiniteChannel X (Y j)) (j : J) :
    (code.onReceiver channels j).rate = code.rate := rfl

@[simp, capacity_shared_api]
theorem onReceiver_messageCount (code : BlockCode X Y n)
    (channels : (j : J) → FiniteChannel X (Y j)) (j : J) :
    (code.onReceiver channels j).messageCount = code.messageCount := rfl

@[simp, capacity_shared_api]
theorem oneMessage_averageErrorProbability [Nonempty X]
    (channels : (j : J) → FiniteChannel X (Y j)) (n : ℕ) (j : J) :
    (oneMessage (X := X) (Y := Y) n).averageErrorProbability channels j = 0 := by
  exact FiniteChannel.BlockCode.oneMessage_averageErrorProbability (channels j) n

end BlockCode

variable [Fintype X] [∀ j, Fintype (Y j)]

/-- One code is reliable at every receiver at every sufficiently large blocklength. -/
@[capacity_shared_api]
def AchievableRate (channels : (j : J) → FiniteChannel X (Y j)) (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ firstBlocklength : ℕ, 0 < firstBlocklength ∧
    ∀ blocklength, firstBlocklength ≤ blocklength →
      ∃ code : BlockCode X Y blocklength,
        (∀ j, code.averageErrorProbability channels j ≤ ε) ∧ rate ≤ code.rate

/-- The one-message code achieves every nonpositive rate at all receivers. -/
@[capacity_shared_api]
theorem achievableRate_of_nonpos [Nonempty X]
    (channels : (j : J) → FiniteChannel X (Y j)) {rate : ℝ} (hrate : rate ≤ 0) :
    AchievableRate channels rate := by
  intro ε hε
  refine ⟨1, by omega, ?_⟩
  intro n _
  refine ⟨BlockCode.oneMessage n, ?_, ?_⟩
  · intro j
    simpa using hε.le
  · simpa using hrate

/-- Common-message capacity in bits per use, including zero in the rate set. -/
@[capacity_shared_api]
noncomputable def operationalCapacityBits (channels : (j : J) → FiniteChannel X (Y j)) : ℝ :=
  sSup {rate | rate = 0 ∨ AchievableRate channels rate}

/-- The marginal observation channel for each receiver of a joint broadcast channel. -/
@[capacity_shared_api]
noncomputable def receiverChannels [Fintype J] [DecidableEq J]
    (channel : FiniteChannel X ((j : J) → Y j)) (j : J) : FiniteChannel X (Y j) := by
  classical
  exact channel.relabelOutput (fun output ↦ output j)

end CapacityAtlas.CommonMessageBroadcast
