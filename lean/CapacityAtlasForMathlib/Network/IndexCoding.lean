/-
Copyright 2026 The Capacity Atlas Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import CapacityAtlasUtil.Metadata
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic

open scoped BigOperators

namespace CapacityAtlas.IndexCoding

/-- A finite index-coding instance with independent messages and arbitrary receivers. -/
@[capacity_shared_api]
structure Instance (Message Receiver : Type*) [DecidableEq Message] where
  demand : Receiver → Message
  sideInformation : Receiver → Finset Message
  demand_not_sideInformation : ∀ receiver, demand receiver ∉ sideInformation receiver

namespace Instance

variable {Message Receiver : Type*} [Fintype Message] [DecidableEq Message]

/-- Messages unknown at a receiver, excluding its demanded message. -/
@[capacity_shared_api]
def interference (problem : Instance Message Receiver) (receiver : Receiver) :
    Finset Message :=
  (Finset.univ.erase (problem.demand receiver)) \ problem.sideInformation receiver

/-- Build an instance from the source convention that lists unknown interferers. -/
@[capacity_shared_api]
def fromInterference (demand : Receiver → Message)
    (interference : Receiver → Finset Message) :
    Instance Message Receiver where
  demand := demand
  sideInformation receiver :=
    (Finset.univ.erase (demand receiver)) \ interference receiver
  demand_not_sideInformation receiver := by simp

@[simp, capacity_shared_api]
theorem interference_fromInterference (demand : Receiver → Message)
    (listedInterference : Receiver → Finset Message)
    (_demand_not_interference : ∀ receiver, demand receiver ∉ listedInterference receiver)
    (receiver : Receiver) :
    (fromInterference demand listedInterference).interference receiver =
      listedInterference receiver := by
  ext message
  by_cases hdemand : message = demand receiver
  · subst message
    simp [interference, fromInterference, _demand_not_interference receiver]
  · simp [interference, fromInterference, hdemand]

end Instance

/-- A deterministic index code with separate message and broadcast alphabets. -/
@[capacity_shared_api]
structure Code {Message Receiver : Type*} [DecidableEq Message]
    (problem : Instance Message Receiver)
    (MessageAlphabet BroadcastAlphabet : Type*)
    (messageLength broadcastLength : ℕ) where
  encode :
    (Message → Fin messageLength → MessageAlphabet) →
      Fin broadcastLength → BroadcastAlphabet
  decode :
    (receiver : Receiver) →
    (Fin broadcastLength → BroadcastAlphabet) →
    ((message : Message) → message ∈ problem.sideInformation receiver →
      Fin messageLength → MessageAlphabet) →
    Fin messageLength → MessageAlphabet

namespace Code

variable {Message Receiver MessageAlphabet BroadcastAlphabet : Type*}
variable [DecidableEq Message]
variable {problem : Instance Message Receiver}
variable {messageLength broadcastLength : ℕ}

/-- The symbol produced by a receiver when all messages equal `messages`. -/
@[capacity_shared_api]
def decodedSymbol
    (code : Code problem MessageAlphabet BroadcastAlphabet messageLength broadcastLength)
    (messages : Message → Fin messageLength → MessageAlphabet)
    (receiver : Receiver) (coordinate : Fin messageLength) : MessageAlphabet :=
  code.decode receiver (code.encode messages)
    (fun message _ ↦ messages message) coordinate

/-- Exact decoding for every message tuple, receiver, and coordinate. -/
@[capacity_shared_api]
def IsZeroError
    (code : Code problem MessageAlphabet BroadcastAlphabet messageLength broadcastLength) : Prop :=
  ∀ messages receiver coordinate,
    code.decodedSymbol messages receiver coordinate =
      messages (problem.demand receiver) coordinate

/-- Uniform-message average block-error probability. -/
@[capacity_shared_api]
noncomputable def AverageErrorProbability
    [Fintype Message] [Fintype Receiver] [Fintype MessageAlphabet]
    [DecidableEq MessageAlphabet] [Nonempty MessageAlphabet]
    (code : Code problem MessageAlphabet BroadcastAlphabet messageLength broadcastLength) : ℝ :=
  let MessageTuple := Message → Fin messageLength → MessageAlphabet
  (Fintype.card MessageTuple : ℝ)⁻¹ *
    ∑ messages : MessageTuple,
      if ∀ receiver coordinate,
          code.decodedSymbol messages receiver coordinate =
            messages (problem.demand receiver) coordinate then 0 else 1

/-- Message symbols per broadcast symbol for a common alphabet. -/
@[capacity_shared_api]
noncomputable def symmetricRate (messageLength broadcastLength : ℕ) : ℝ :=
  (messageLength : ℝ) / broadcastLength

end Code

variable {Message Receiver : Type*}
variable [Fintype Message] [DecidableEq Message] [Fintype Receiver]

/-- Zero-error symmetric achievability over one fixed finite alphabet. -/
@[capacity_shared_api]
def AchievableSymmetricRateOver (problem : Instance Message Receiver)
    (Alphabet : Type*) [Fintype Alphabet] [DecidableEq Alphabet]
    (rate : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ firstBroadcastLength : ℕ,
    ∃ messageLength broadcastLength : ℕ,
      firstBroadcastLength ≤ broadcastLength ∧ 0 < broadcastLength ∧
      ∃ code : Code problem Alphabet Alphabet messageLength broadcastLength,
        code.IsZeroError ∧
          rate - δ ≤ Code.symmetricRate messageLength broadcastLength

/-- Zero-error symmetric achievability over an arbitrary nontrivial finite alphabet. -/
@[capacity_shared_api]
def AchievableSymmetricRate (problem : Instance Message Receiver) (rate : ℝ) : Prop :=
  ∃ alphabetCard : ℕ, 2 ≤ alphabetCard ∧
    AchievableSymmetricRateOver problem (Fin alphabetCard) rate

/-- Zero-error symmetric capacity, allowing arbitrary finite alphabets and blocklengths. -/
@[capacity_shared_api]
noncomputable def symmetricCapacity (problem : Instance Message Receiver) : ℝ :=
  sSup {rate | AchievableSymmetricRate problem rate}

/-- Vanishing uniform-average-error achievability over one fixed alphabet. -/
@[capacity_shared_api]
def AchievableVanishingErrorSymmetricRateOver (problem : Instance Message Receiver)
    (Alphabet : Type*) [Fintype Alphabet] [DecidableEq Alphabet] [Nonempty Alphabet]
    (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ firstBroadcastLength : ℕ,
    ∃ messageLength broadcastLength : ℕ,
      firstBroadcastLength ≤ broadcastLength ∧ 0 < broadcastLength ∧
      ∃ code : Code problem Alphabet Alphabet messageLength broadcastLength,
        code.AverageErrorProbability ≤ ε ∧
          rate - δ ≤ Code.symmetricRate messageLength broadcastLength

/-- Vanishing-average-error symmetric capacity over one fixed finite alphabet. -/
@[capacity_shared_api]
noncomputable def vanishingErrorSymmetricCapacityOver
    (problem : Instance Message Receiver)
    (Alphabet : Type*) [Fintype Alphabet] [DecidableEq Alphabet] [Nonempty Alphabet] : ℝ :=
  sSup {rate | AchievableVanishingErrorSymmetricRateOver problem Alphabet rate}

/-- The encoder of an index code is linear; its receivers may decode nonlinearly. -/
@[capacity_shared_api]
def Code.IsLinearEncoder {FieldAlphabet : Type*} [Field FieldAlphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem FieldAlphabet FieldAlphabet messageLength broadcastLength) : Prop :=
  code.encode 0 = 0 ∧
    (∀ left right, code.encode (left + right) = code.encode left + code.encode right) ∧
    ∀ (scalar : FieldAlphabet) messages,
      code.encode (scalar • messages) = scalar • code.encode messages

/-- Zero-error vector-linear achievability over a fixed finite field. -/
@[capacity_shared_api]
def AchievableLinearSymmetricRateOver (problem : Instance Message Receiver)
    (FieldAlphabet : Type*) [Fintype FieldAlphabet] [DecidableEq FieldAlphabet]
    [Field FieldAlphabet] (rate : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ firstBroadcastLength : ℕ,
    ∃ messageLength broadcastLength : ℕ,
      firstBroadcastLength ≤ broadcastLength ∧ 0 < broadcastLength ∧
      ∃ code : Code problem FieldAlphabet FieldAlphabet messageLength broadcastLength,
        code.IsZeroError ∧ code.IsLinearEncoder ∧
          rate - δ ≤ Code.symmetricRate messageLength broadcastLength

/-- Vector-linear symmetric capacity over a specified finite field. -/
@[capacity_shared_api]
noncomputable def linearSymmetricCapacityOver (problem : Instance Message Receiver)
    (FieldAlphabet : Type*) [Fintype FieldAlphabet] [DecidableEq FieldAlphabet]
    [Field FieldAlphabet] : ℝ :=
  sSup {rate | AchievableLinearSymmetricRateOver problem FieldAlphabet rate}

/-- A finite field packaged so capacities can be compared across characteristics and extensions. -/
@[capacity_shared_api]
structure FiniteFieldModel where
  Carrier : Type
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier
  field : Field Carrier

@[capacity_shared_api]
noncomputable def linearSymmetricCapacityForModel (problem : Instance Message Receiver)
    (model : FiniteFieldModel) : ℝ := by
  letI := model.fintype
  letI := model.decidableEq
  letI := model.field
  exact linearSymmetricCapacityOver problem model.Carrier

/-- Global vector-linear capacity: the supremum over every finite field model. -/
@[capacity_shared_api]
noncomputable def linearSymmetricCapacity (problem : Instance Message Receiver) : ℝ :=
  sSup (Set.range (linearSymmetricCapacityForModel problem))

/-- Feasibility in the normalized symmetric Shannon-polymatroid outer relaxation. -/
@[capacity_shared_api]
def ShannonPolymatroidFeasible (problem : Instance Message Receiver) (rate : ℝ)
    (rank : Finset Message → ℝ) : Prop :=
  rank ∅ = 0 ∧ rank Finset.univ = 1 ∧
    (∀ left right, left ⊆ right → rank left ≤ rank right) ∧
    (∀ left right,
      rank (left ∪ right) + rank (left ∩ right) ≤ rank left + rank right) ∧
    ∀ receiver,
      rate ≤ rank (insert (problem.demand receiver) (problem.interference receiver)) -
        rank (problem.interference receiver)

/-- Best symmetric outer-bound value obtainable from Shannon polymatroid constraints. -/
@[capacity_shared_api]
noncomputable def shannonPolymatroidOuterBound (problem : Instance Message Receiver) : ℝ :=
  sSup {rate | ∃ rank, ShannonPolymatroidFeasible problem rate rank}

end CapacityAtlas.IndexCoding
