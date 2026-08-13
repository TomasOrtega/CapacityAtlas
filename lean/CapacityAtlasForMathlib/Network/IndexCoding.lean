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
import CapacityAtlasForMathlib.InformationTheory.FiniteEntropy
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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

@[capacity_shared_api]
theorem complement_interference (problem : Instance Message Receiver)
    (receiver : Receiver) :
    Finset.univ \ problem.interference receiver =
      insert (problem.demand receiver) (problem.sideInformation receiver) := by
  ext message
  by_cases hdemand : message = problem.demand receiver
  · subst message
    simp [interference, problem.demand_not_sideInformation receiver]
  · simp [interference, hdemand]

@[capacity_shared_api]
theorem complement_insert_interference (problem : Instance Message Receiver)
    (receiver : Receiver) :
    Finset.univ \ insert (problem.demand receiver) (problem.interference receiver) =
      problem.sideInformation receiver := by
  ext message
  by_cases hdemand : message = problem.demand receiver
  · subst message
    simp [problem.demand_not_sideInformation receiver]
  · simp [interference, hdemand]

end Instance

variable {Message Receiver : Type*}
variable [Fintype Message] [DecidableEq Message] [Fintype Receiver]

/-- Distinct messages are aligned when they interfere at a common receiver. -/
@[capacity_shared_api]
def AreAligned (problem : Instance Message Receiver) (left right : Message) : Prop :=
  left ≠ right ∧ ∃ receiver,
    left ∈ problem.interference receiver ∧
      right ∈ problem.interference receiver

/-- The graph associated with the abstract alignment relation. -/
@[capacity_shared_api]
def alignmentGraph (problem : Instance Message Receiver) : SimpleGraph Message :=
  SimpleGraph.fromRel (AreAligned problem)

instance (problem : Instance Message Receiver) :
    DecidableRel (alignmentGraph problem).Adj := by
  intro left right
  unfold alignmentGraph AreAligned
  infer_instance

/-- Two messages conflict when one is demanded where the other is unknown. -/
@[capacity_shared_api]
def IsConflict (problem : Instance Message Receiver) (left right : Message) : Prop :=
  ∃ receiver,
    (problem.demand receiver = left ∧ right ∈ problem.interference receiver) ∨
      (problem.demand receiver = right ∧ left ∈ problem.interference receiver)

instance (problem : Instance Message Receiver) (left right : Message) :
    Decidable (IsConflict problem left right) := by
  unfold IsConflict
  infer_instance

/-- An internal conflict is a conflict inside one alignment-graph component. -/
@[capacity_shared_api]
def IsInternalConflict (problem : Instance Message Receiver) (left right : Message) : Prop :=
  IsConflict problem left right ∧ (alignmentGraph problem).Reachable left right


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

/-- Transport a code along an equivalence of its common alphabet. -/
@[capacity_shared_api]
def relabelAlphabet {Alphabet NewAlphabet : Type*}
    (equiv : Alphabet ≃ NewAlphabet)
    (code : Code problem Alphabet Alphabet messageLength broadcastLength) :
    Code problem NewAlphabet NewAlphabet messageLength broadcastLength where
  encode messages coordinate :=
    equiv (code.encode (fun message index ↦ equiv.symm (messages message index)) coordinate)
  decode receiver broadcast sideInformation coordinate :=
    equiv (code.decode receiver (fun index ↦ equiv.symm (broadcast index))
      (fun message h index ↦ equiv.symm (sideInformation message h index)) coordinate)

@[capacity_shared_api]
theorem relabelAlphabet_isZeroError {Alphabet NewAlphabet : Type*}
    (equiv : Alphabet ≃ NewAlphabet)
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (hzero : code.IsZeroError) : (code.relabelAlphabet equiv).IsZeroError := by
  intro messages receiver coordinate
  simp only [decodedSymbol, relabelAlphabet]
  simp only [equiv.symm_apply_apply]
  change equiv (code.decodedSymbol
    (fun message index ↦ equiv.symm (messages message index)) receiver coordinate) = _
  rw [hzero]
  exact equiv.apply_symm_apply _

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

/-- Zero-error achievability with a linear encoder over a fixed finite field.

Decoder linearity is intentionally not required. -/
@[capacity_shared_api]
def AchievableLinearEncoderSymmetricRateOver (problem : Instance Message Receiver)
    (FieldAlphabet : Type*) [Fintype FieldAlphabet] [DecidableEq FieldAlphabet]
    [Field FieldAlphabet] (rate : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ firstBroadcastLength : ℕ,
    ∃ messageLength broadcastLength : ℕ,
      firstBroadcastLength ≤ broadcastLength ∧ 0 < broadcastLength ∧
      ∃ code : Code problem FieldAlphabet FieldAlphabet messageLength broadcastLength,
        code.IsZeroError ∧ code.IsLinearEncoder ∧
          rate - δ ≤ Code.symmetricRate messageLength broadcastLength

/-- Symmetric capacity with a linear encoder over a specified finite field. -/
@[capacity_shared_api]
noncomputable def linearEncoderSymmetricCapacityOver (problem : Instance Message Receiver)
    (FieldAlphabet : Type*) [Fintype FieldAlphabet] [DecidableEq FieldAlphabet]
    [Field FieldAlphabet] : ℝ :=
  sSup {rate | AchievableLinearEncoderSymmetricRateOver problem FieldAlphabet rate}

/-- A finite field packaged so capacities can be compared across characteristics and extensions. -/
@[capacity_shared_api]
structure FiniteFieldModel where
  Carrier : Type
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier
  field : Field Carrier

@[capacity_shared_api]
noncomputable def linearEncoderSymmetricCapacityForModel (problem : Instance Message Receiver)
    (model : FiniteFieldModel) : ℝ := by
  letI := model.fintype
  letI := model.decidableEq
  letI := model.field
  exact linearEncoderSymmetricCapacityOver problem model.Carrier

/-- Global linear-encoder capacity: the supremum over every finite field model. -/
@[capacity_shared_api]
noncomputable def linearEncoderSymmetricCapacity (problem : Instance Message Receiver) : ℝ :=
  sSup (Set.range (linearEncoderSymmetricCapacityForModel problem))

omit [Fintype Message] [Fintype Receiver] in
private theorem zeroRate_linearEncoderAchievable
    (problem : Instance Message Receiver) (FieldAlphabet : Type*)
    [Fintype FieldAlphabet] [DecidableEq FieldAlphabet] [Field FieldAlphabet] :
    AchievableLinearEncoderSymmetricRateOver problem FieldAlphabet 0 := by
  intro δ hδ firstBroadcastLength
  let code : Code problem FieldAlphabet FieldAlphabet 0 (firstBroadcastLength + 1) :=
    { encode := fun _ _ ↦ 0
      decode := fun _ _ _ coordinate ↦ Fin.elim0 coordinate }
  exact ⟨0, firstBroadcastLength + 1, Nat.le_add_right _ _, Nat.zero_lt_succ _, code,
    (by intro _ _ coordinate; exact Fin.elim0 coordinate),
    (by
      unfold Code.IsLinearEncoder
      constructor
      · funext coordinate
        simp [code]
      · constructor <;> intros <;> funext coordinate <;> simp [code]),
    by simp [Code.symmetricRate, hδ.le]⟩

omit [Fintype Message] [Fintype Receiver] in
private theorem Code.symmetricRate_le_one_of_zeroError
    [Nonempty Receiver] {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    [Nontrivial Alphabet]
    (problem : Instance Message Receiver)
    {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (hzero : code.IsZeroError) (hbroadcast : 0 < broadcastLength) :
    Code.symmetricRate messageLength broadcastLength ≤ 1 := by
  let receiver : Receiver := Classical.choice (inferInstance : Nonempty Receiver)
  let fallback : Alphabet := Classical.choice (inferInstance : Nonempty Alphabet)
  let fill : (Fin messageLength → Alphabet) → Message → Fin messageLength → Alphabet :=
    fun word message coordinate ↦
      if message = problem.demand receiver then word coordinate else fallback
  let broadcast : (Fin messageLength → Alphabet) → Fin broadcastLength → Alphabet :=
    fun word ↦ code.encode (fill word)
  have hinjective : Function.Injective broadcast := by
    intro left right heq
    funext coordinate
    have hleft : code.decode receiver (broadcast left)
        (fun message _ ↦ fill left message) coordinate = left coordinate := by
      simpa [Code.decodedSymbol, broadcast, fill] using
        hzero (fill left) receiver coordinate
    have hright : code.decode receiver (broadcast right)
        (fun message _ ↦ fill right message) coordinate = right coordinate := by
      simpa [Code.decodedSymbol, broadcast, fill] using
        hzero (fill right) receiver coordinate
    rw [heq] at hleft
    have hside :
        (fun message (_ : message ∈ problem.sideInformation receiver) ↦ fill left message) =
          fun message (_ : message ∈ problem.sideInformation receiver) ↦ fill right message := by
      funext message hmessage coordinate
      simp [fill, ne_of_mem_of_not_mem hmessage (problem.demand_not_sideInformation receiver)]
    rw [hside] at hleft
    exact hleft.symm.trans hright
  have hcard := Fintype.card_le_of_injective broadcast hinjective
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  have hlength : messageLength ≤ broadcastLength :=
    (Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp hcard
  unfold Code.symmetricRate
  exact (div_le_one (by positivity)).2 (by exact_mod_cast hlength)

omit [Fintype Message] [Fintype Receiver] in
private theorem achievableSymmetricRate_le_one [Nonempty Receiver]
    (problem : Instance Message Receiver) {rate : ℝ}
    (hrate : AchievableSymmetricRate problem rate) : rate ≤ 1 := by
  rcases hrate with ⟨alphabetCard, halphabetCard, hrate⟩
  letI : Nontrivial (Fin alphabetCard) := Fin.nontrivial_iff_two_le.mpr halphabetCard
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨messageLength, broadcastLength, _, hbroadcastLength, code, hzero, hclose⟩ :=
    hrate δ hδ 0
  have hcode := Code.symmetricRate_le_one_of_zeroError problem code hzero hbroadcastLength
  linarith

omit [Fintype Message] [Fintype Receiver] in
private theorem achievableSymmetricRate_bounded [Nonempty Receiver]
    (problem : Instance Message Receiver) :
    BddAbove {rate | AchievableSymmetricRate problem rate} :=
  ⟨1, fun _ hrate ↦ achievableSymmetricRate_le_one problem hrate⟩

omit [Fintype Message] [Fintype Receiver] in
private theorem achievableLinearEncoderSymmetricRate_le_one [Nonempty Receiver]
    (problem : Instance Message Receiver) (FieldAlphabet : Type*)
    [Fintype FieldAlphabet] [DecidableEq FieldAlphabet] [Field FieldAlphabet]
    {rate : ℝ}
    (hrate : AchievableLinearEncoderSymmetricRateOver problem FieldAlphabet rate) : rate ≤ 1 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨messageLength, broadcastLength, _, hbroadcastLength, code, hzero, _, hclose⟩ :=
    hrate δ hδ 0
  have hcode := Code.symmetricRate_le_one_of_zeroError problem code hzero hbroadcastLength
  linarith

omit [Fintype Message] [Fintype Receiver] in
private theorem achievableLinearEncoderSymmetricRate_bounded [Nonempty Receiver]
    (problem : Instance Message Receiver) (FieldAlphabet : Type*)
    [Fintype FieldAlphabet] [DecidableEq FieldAlphabet] [Field FieldAlphabet] :
    BddAbove {rate | AchievableLinearEncoderSymmetricRateOver problem FieldAlphabet rate} :=
  ⟨1, fun _ hrate ↦
    achievableLinearEncoderSymmetricRate_le_one problem FieldAlphabet hrate⟩

/- Every rate achievable with a linear encoder is achievable without that restriction. -/
omit [Fintype Message] [Fintype Receiver] in
theorem linearEncoderAchievable_implies_achievable
    (problem : Instance Message Receiver) (FieldAlphabet : Type*)
    [Fintype FieldAlphabet] [DecidableEq FieldAlphabet] [Field FieldAlphabet]
    {rate : ℝ} (hrate : AchievableLinearEncoderSymmetricRateOver problem FieldAlphabet rate) :
    AchievableSymmetricRate problem rate := by
  let equiv := Fintype.equivFin FieldAlphabet
  refine ⟨Fintype.card FieldAlphabet, Fintype.one_lt_card, ?_⟩
  intro δ hδ firstBroadcastLength
  obtain ⟨messageLength, broadcastLength, hfirst, hbroadcast, code, hzero, _, hrate⟩ :=
    hrate δ hδ firstBroadcastLength
  exact ⟨messageLength, broadcastLength, hfirst, hbroadcast,
    code.relabelAlphabet equiv, code.relabelAlphabet_isZeroError equiv hzero, hrate⟩

attribute [capacity_shared_api] linearEncoderAchievable_implies_achievable

/- A fixed-field linear-encoder capacity is bounded by the global one. -/
omit [Fintype Message] [Fintype Receiver] in
theorem linearEncoderSymmetricCapacityOver_le_linearEncoderSymmetricCapacity
    [Nonempty Receiver] (problem : Instance Message Receiver) (FieldAlphabet : Type)
    [Fintype FieldAlphabet] [DecidableEq FieldAlphabet] [Field FieldAlphabet] :
    linearEncoderSymmetricCapacityOver problem FieldAlphabet ≤
      linearEncoderSymmetricCapacity problem := by
  apply le_csSup
  · use 1
    intro value hvalue
    rcases hvalue with ⟨model, rfl⟩
    letI := model.fintype
    letI := model.decidableEq
    letI := model.field
    apply csSup_le
    · exact ⟨0, zeroRate_linearEncoderAchievable problem model.Carrier⟩
    · intro rate hrate
      exact achievableLinearEncoderSymmetricRate_le_one problem model.Carrier hrate
  · let model : FiniteFieldModel :=
      { Carrier := FieldAlphabet
        fintype := inferInstance
        decidableEq := inferInstance
        field := inferInstance }
    exact ⟨model, rfl⟩

attribute [capacity_shared_api]
  linearEncoderSymmetricCapacityOver_le_linearEncoderSymmetricCapacity

/- Linear-encoder capacity is no larger than unrestricted symmetric capacity. -/
omit [Fintype Message] [Fintype Receiver] in
theorem linearEncoderSymmetricCapacity_le_symmetricCapacity
    [Nonempty Receiver] (problem : Instance Message Receiver) :
    linearEncoderSymmetricCapacity problem ≤ symmetricCapacity problem := by
  let binaryModel : FiniteFieldModel :=
    { Carrier := ZMod 2
      fintype := inferInstance
      decidableEq := inferInstance
      field := inferInstance }
  apply csSup_le
  · exact ⟨linearEncoderSymmetricCapacityForModel problem binaryModel,
      binaryModel, rfl⟩
  · intro value hvalue
    rcases hvalue with ⟨model, rfl⟩
    letI := model.fintype
    letI := model.decidableEq
    letI := model.field
    apply csSup_le
    · exact ⟨0, zeroRate_linearEncoderAchievable problem model.Carrier⟩
    · intro rate hrate
      apply le_csSup (achievableSymmetricRate_bounded problem)
      exact linearEncoderAchievable_implies_achievable problem model.Carrier hrate

attribute [capacity_shared_api] linearEncoderSymmetricCapacity_le_symmetricCapacity

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

namespace ShannonCertificate

private def restrictValues {I A : Type*} (set : Finset I) (values : I → A) :
    {i // i ∈ set} → A := fun index ↦ values index

private def restrictSubset {I A : Type*} {small large : Finset I} (h : small ⊆ large)
    (values : {i // i ∈ large} → A) : {i // i ∈ small} → A :=
  fun index ↦ values ⟨index, h index.property⟩

private def mergeRestrictions {I A : Type*} [DecidableEq I] (left right : Finset I)
    (values : ({i // i ∈ left} → A) × ({i // i ∈ right} → A)) :
    {i // i ∈ left ∪ right} → A :=
  fun index ↦ if h : index.1 ∈ left then values.1 ⟨index, h⟩
    else values.2 ⟨index, (Finset.mem_union.mp index.property).resolve_left h⟩

private theorem entropy_map_eq_of_mutually_determined
    {Source Left Right : Type*} [Fintype Source] [Fintype Left] [Fintype Right]
    [DecidableEq Left] [DecidableEq Right]
    (distribution : FiniteDistribution Source) (left : Source → Left)
    (right : Source → Right) (toRight : Left → Right) (toLeft : Right → Left)
    (hRight : toRight ∘ left = right) (hLeft : toLeft ∘ right = left) :
    (distribution.map left).entropy = (distribution.map right).entropy := by
  apply le_antisymm
  · have h := (distribution.map right).entropy_map_le toLeft
    rw [FiniteDistribution.map_map, hLeft] at h
    exact h
  · have h := (distribution.map left).entropy_map_le toRight
    rw [FiniteDistribution.map_map, hRight] at h
    exact h

private theorem uniform_map_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] [DecidableEq Y] (equiv : X ≃ Y) :
    (FiniteDistribution.uniform X).map equiv = FiniteDistribution.uniform Y := by
  ext y
  change (∑ x with equiv x = y, (Fintype.card X : ℝ)⁻¹) =
    (Fintype.card Y : ℝ)⁻¹
  rw [show Finset.univ.filter (fun x ↦ equiv x = y) = {equiv.symm y} by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact equiv.injective (h.trans (equiv.apply_symm_apply y).symm)
    · rintro rfl
      exact equiv.apply_symm_apply y]
  simp [Fintype.card_congr equiv]

private theorem uniform_prod_map_fst {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] [DecidableEq X] :
    (FiniteDistribution.uniform (X × Y)).map Prod.fst = FiniteDistribution.uniform X := by
  ext x
  change (∑ z : X × Y with z.1 = x, (Fintype.card (X × Y) : ℝ)⁻¹) =
    (Fintype.card X : ℝ)⁻¹
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hcardY : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Fintype.card_prod, hcardY]

private theorem uniform_pi_restrict {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Nonempty A] (set : Finset I) :
    (FiniteDistribution.uniform (I → A)).map (restrictValues set) =
      FiniteDistribution.uniform ({i // i ∈ set} → A) := by
  let equiv := Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ set) (fun _ ↦ A)
  have hcomp : restrictValues set = Prod.fst ∘ equiv := by
    funext values index
    rfl
  rw [hcomp, ← FiniteDistribution.map_map]
  rw [uniform_map_equiv equiv]
  exact uniform_prod_map_fst

private theorem entropy_pi_restrict_uniform {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Nonempty A] (set : Finset I) :
    ((FiniteDistribution.uniform (I → A)).map (restrictValues set)).entropy =
      (set.card : ℝ) * Real.log (Fintype.card A) := by
  rw [uniform_pi_restrict set, FiniteDistribution.entropy_uniform]
  simp only [Fintype.card_fun, Fintype.card_coe]
  rw [Nat.cast_pow, Real.log_pow]

private theorem entropy_broadcast_restrict_submodular
    {I A Source Broadcast : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    [Fintype Source] [Fintype Broadcast] [DecidableEq Broadcast]
    (distribution : FiniteDistribution Source) (messages : Source → I → A)
    (broadcast : Source → Broadcast) (left right : Finset I) :
    (distribution.map (fun source ↦
        (broadcast source, restrictValues (left ∪ right) (messages source)))).entropy +
      (distribution.map (fun source ↦
        (broadcast source, restrictValues (left ∩ right) (messages source)))).entropy ≤
      (distribution.map (fun source ↦
        (broadcast source, restrictValues left (messages source)))).entropy +
      (distribution.map (fun source ↦
        (broadcast source, restrictValues right (messages source)))).entropy := by
  let observe (set : Finset I) (source : Source) :=
    (broadcast source, restrictValues set (messages source))
  have hssa := distribution.entropy_map_strong_subadditivity
    (observe left) (observe right) (observe (left ∩ right))
  have htriple :
      (distribution.map fun source ↦
        (observe left source, (observe right source, observe (left ∩ right) source))).entropy =
      (distribution.map (observe (left ∪ right))).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _
      (fun observations ↦
        (observations.1.1, mergeRestrictions left right
          (observations.1.2, observations.2.1.2)))
      (fun observation ↦
        ((observation.1, restrictSubset Finset.subset_union_left observation.2),
          ((observation.1, restrictSubset Finset.subset_union_right observation.2),
            (observation.1, restrictSubset
              (Finset.inter_subset_left.trans Finset.subset_union_left) observation.2))))
    · funext source
      ext <;> simp [observe, mergeRestrictions, restrictValues]
    · funext source
      ext <;> simp [observe, restrictSubset, restrictValues]
  have hleft :
      (distribution.map fun source ↦
        (observe left source, observe (left ∩ right) source)).entropy =
      (distribution.map (observe left)).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _ Prod.fst
      (fun observation ↦
        (observation, (observation.1,
          restrictSubset Finset.inter_subset_left observation.2)))
    · rfl
    · funext source
      ext <;> simp [observe, restrictSubset, restrictValues]
  have hright :
      (distribution.map fun source ↦
        (observe right source, observe (left ∩ right) source)).entropy =
      (distribution.map (observe right)).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _ Prod.fst
      (fun observation ↦
        (observation, (observation.1,
          restrictSubset Finset.inter_subset_right observation.2)))
    · rfl
    · funext source
      ext <;> simp [observe, restrictSubset, restrictValues]
  rw [htriple, hleft, hright] at hssa
  exact hssa

private theorem entropy_broadcast_restrict_conditioning
    {I A Source Broadcast : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    [Fintype Source] [Fintype Broadcast] [DecidableEq Broadcast]
    (distribution : FiniteDistribution Source) (messages : Source → I → A)
    (broadcast : Source → Broadcast) {small large : Finset I} (hsubset : small ⊆ large) :
    (distribution.map (fun source ↦
        (broadcast source, restrictValues large (messages source)))).entropy +
      (distribution.map (fun source ↦ restrictValues small (messages source))).entropy ≤
      (distribution.map (fun source ↦ restrictValues large (messages source))).entropy +
      (distribution.map (fun source ↦
        (broadcast source, restrictValues small (messages source)))).entropy := by
  let largeObservation (source : Source) := restrictValues large (messages source)
  let smallObservation (source : Source) := restrictValues small (messages source)
  have hssa := distribution.entropy_map_strong_subadditivity broadcast
    largeObservation smallObservation
  have htriple :
      (distribution.map fun source ↦
        (broadcast source, (largeObservation source, smallObservation source))).entropy =
      (distribution.map fun source ↦
        (broadcast source, largeObservation source)).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _
      (fun observation ↦ (observation.1, observation.2.1))
      (fun observation ↦
        (observation.1, (observation.2, restrictSubset hsubset observation.2)))
    · rfl
    · funext source
      ext <;> simp [largeObservation, smallObservation, restrictSubset, restrictValues]
  have hlargePair :
      (distribution.map fun source ↦
        (largeObservation source, smallObservation source)).entropy =
      (distribution.map largeObservation).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _ Prod.fst
      (fun observation ↦ (observation, restrictSubset hsubset observation))
    · rfl
    · funext source
      ext <;> simp [largeObservation, smallObservation, restrictSubset, restrictValues]
  rw [htriple, hlargePair] at hssa
  simpa [largeObservation, smallObservation, add_comm] using hssa

private theorem entropy_restrict_subset_difference
    {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (distribution : FiniteDistribution (I → A))
    {small large : Finset I} (hsubset : small ⊆ large) :
    (distribution.map (restrictValues large)).entropy -
        (distribution.map (restrictValues small)).entropy ≤
      (distribution.map (restrictValues (large \ small))).entropy := by
  have hssa := distribution.entropy_map_strong_subadditivity
    (restrictValues small) (restrictValues (large \ small)) (fun _ ↦ Unit.unit)
  have hempty : (distribution.map fun _ ↦ Unit.unit).entropy = 0 := by
    have hle := (distribution.map fun _ ↦ Unit.unit).entropy_le_log_card
    have hnonnegative := (distribution.map fun _ ↦ Unit.unit).entropy_nonnegative
    norm_num at hle
    exact le_antisymm hle hnonnegative
  have hunion : small ∪ (large \ small) = large := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact hsubset h
      · exact h.1
    · intro h
      by_cases hs : i ∈ small
      · exact Or.inl hs
      · exact Or.inr ⟨h, hs⟩
  have htriple :
      (distribution.map fun source ↦
        (restrictValues small source,
          (restrictValues (large \ small) source, Unit.unit))).entropy =
      (distribution.map (restrictValues large)).entropy := by
    let join : (({i // i ∈ small} → A) ×
        (({i // i ∈ large \ small} → A) × Unit)) →
        {i // i ∈ large} → A := fun observations index ↦
      if h : index.1 ∈ small then observations.1 ⟨index, h⟩
      else observations.2.1 ⟨index, Finset.mem_sdiff.mpr ⟨index.property, h⟩⟩
    apply entropy_map_eq_of_mutually_determined distribution _ _ join
      (fun observation ↦
        (restrictSubset hsubset observation,
          (restrictSubset Finset.sdiff_subset observation, Unit.unit)))
    · funext source
      ext index
      simp only [Function.comp_apply, join, restrictValues]
      split_ifs <;> rfl
    · funext source
      ext <;> simp [restrictValues, restrictSubset]
  have hsmall :
      (distribution.map fun source ↦
        (restrictValues small source, Unit.unit)).entropy =
      (distribution.map (restrictValues small)).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _ Prod.fst
      (fun observation ↦ (observation, Unit.unit)) <;> rfl
  have hdiff :
      (distribution.map fun source ↦
        (restrictValues (large \ small) source, Unit.unit)).entropy =
      (distribution.map (restrictValues (large \ small))).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _ Prod.fst
      (fun observation ↦ (observation, Unit.unit)) <;> rfl
  rw [htriple, hempty, hsmall, hdiff] at hssa
  linarith

private def addDecodedDemand {Alphabet : Type*}
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (receiver : Receiver)
    (observation :
      (Fin broadcastLength → Alphabet) ×
        ({message // message ∈ problem.sideInformation receiver} →
          Fin messageLength → Alphabet)) :
    {message // message ∈ insert (problem.demand receiver)
      (problem.sideInformation receiver)} → Fin messageLength → Alphabet :=
  fun message coordinate ↦
    if hdemand : message.1 = problem.demand receiver then
      code.decode receiver observation.1
        (fun sideMessage hside ↦ observation.2 ⟨sideMessage, hside⟩) coordinate
    else
      observation.2 ⟨message.1,
        (Finset.mem_insert.mp message.2).resolve_left hdemand⟩ coordinate

omit [Fintype Receiver] in
private theorem entropy_broadcast_complement_interference_insert
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (hzero : code.IsZeroError) (receiver : Receiver)
    (distribution : FiniteDistribution (Message → Fin messageLength → Alphabet)) :
    (distribution.map (fun messages ↦
        (code.encode messages,
          restrictValues (Finset.univ \ insert (problem.demand receiver)
            (problem.interference receiver)) messages))).entropy =
      (distribution.map (fun messages ↦
        (code.encode messages,
          restrictValues (Finset.univ \ problem.interference receiver) messages))).entropy := by
  rw [Instance.complement_insert_interference, Instance.complement_interference]
  apply entropy_map_eq_of_mutually_determined distribution _ _
    (fun observation ↦ (observation.1, addDecodedDemand code receiver observation))
    (fun observation ↦ (observation.1,
      fun message ↦ observation.2 ⟨message.1, Finset.mem_insert_of_mem message.2⟩))
  · funext messages
    apply Prod.ext
    · rfl
    · funext message coordinate
      by_cases hdemand : message.1 = problem.demand receiver
      · simp only [Function.comp_apply, addDecodedDemand, hdemand, dite_true]
        change code.decodedSymbol messages receiver coordinate = messages message.1 coordinate
        rw [hzero, hdemand]
      · simp [Function.comp_apply, addDecodedDemand, hdemand, restrictValues]
  · rfl

omit [Fintype Receiver] in
private theorem demand_not_interference (problem : Instance Message Receiver)
    (receiver : Receiver) :
    problem.demand receiver ∉ problem.interference receiver := by
  simp [Instance.interference]

private noncomputable def observationEntropy
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nonempty Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (set : Finset Message) : ℝ :=
  ((FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)).map
    (fun messages ↦ (code.encode messages,
      restrictValues (Finset.univ \ set) messages))).entropy

private noncomputable def rawRank
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nonempty Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (set : Finset Message) : ℝ :=
  let symbolEntropy := Real.log (Fintype.card Alphabet)
  let messageEntropy := (messageLength : ℝ) * symbolEntropy
  let totalEntropy := (Fintype.card Message : ℝ) * messageEntropy
  let denominator := (broadcastLength : ℝ) * symbolEntropy
  (observationEntropy code set + (set.card : ℝ) * messageEntropy - totalEntropy) /
    denominator

private theorem denominator_pos {Alphabet : Type*} [Fintype Alphabet] [Nontrivial Alphabet]
    {broadcastLength : ℕ} (hbroadcast : 0 < broadcastLength) :
    0 < (broadcastLength : ℝ) * Real.log (Fintype.card Alphabet) := by
  apply mul_pos
  · exact_mod_cast hbroadcast
  · apply Real.log_pos
    exact_mod_cast Fintype.one_lt_card (α := Alphabet)

omit [Fintype Receiver] in
private theorem observation_empty
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength) :
    observationEntropy code ∅ =
      (Fintype.card Message : ℝ) *
        ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) := by
  let distribution :=
    FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)
  have hobservation :
      (distribution.map (fun messages ↦ (code.encode messages,
        restrictValues Finset.univ messages))).entropy =
      (distribution.map (restrictValues Finset.univ)).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _ Prod.snd
      (fun restricted ↦
        let messages := fun message ↦ restricted ⟨message, Finset.mem_univ message⟩
        (code.encode messages, restricted))
    · rfl
    · funext messages
      apply Prod.ext
      · rfl
      · funext index coordinate
        rfl
  rw [observationEntropy]
  have hobservation' :
      ((FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)).map
        (fun messages ↦ (code.encode messages,
          restrictValues (Finset.univ \ ∅) messages))).entropy =
      ((FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)).map
        (restrictValues Finset.univ)).entropy := by
    have hset : (Finset.univ \ (∅ : Finset Message)) = Finset.univ := by ext; simp
    rw [hset]
    exact hobservation
  rw [hobservation', entropy_pi_restrict_uniform]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [Nat.cast_pow, Real.log_pow]

omit [Fintype Receiver] in
private theorem observation_univ
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength) :
    observationEntropy code Finset.univ =
      ((FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)).map
        code.encode).entropy := by
  let distribution :=
    FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)
  have hobservation :
      (distribution.map (fun messages ↦
        (code.encode messages, restrictValues (∅ : Finset Message) messages))).entropy =
      (distribution.map code.encode).entropy := by
    apply entropy_map_eq_of_mutually_determined distribution _ _ Prod.fst
      (fun broadcast ↦ (broadcast,
        fun index ↦ (Finset.notMem_empty index.1 index.2).elim))
    · rfl
    · funext messages
      apply Prod.ext
      · rfl
      · funext index
        exact (Finset.notMem_empty index.1 index.2).elim
  rw [observationEntropy]
  have hset : (Finset.univ \ (Finset.univ : Finset Message)) = ∅ := by ext; simp
  rw [hset]
  exact hobservation

omit [Fintype Receiver] in
private theorem raw_empty
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength) :
    rawRank code ∅ = 0 := by
  rw [rawRank, observation_empty]
  simp

omit [Fintype Receiver] in
private theorem raw_univ_le_one
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (hbroadcast : 0 < broadcastLength)
    (code : Code problem Alphabet Alphabet messageLength broadcastLength) :
    rawRank code Finset.univ ≤ 1 := by
  have hentropy :
      ((FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)).map
        code.encode).entropy ≤
      (broadcastLength : ℝ) * Real.log (Fintype.card Alphabet) := by
    calc
      _ ≤ Real.log (Fintype.card (Fin broadcastLength → Alphabet)) :=
        FiniteDistribution.entropy_le_log_card _
      _ = _ := by
        simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        rw [Real.log_pow]
  rw [rawRank, observation_univ]
  simp only [Finset.card_univ]
  have hdenom := denominator_pos (Alphabet := Alphabet)
    (broadcastLength := broadcastLength) hbroadcast
  have hcancel :
      ((FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)).map
          code.encode).entropy +
          (Fintype.card Message : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) -
          (Fintype.card Message : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) =
        ((FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)).map
          code.encode).entropy := by ring
  rw [hcancel]
  apply (div_le_one hdenom).2
  exact hentropy

omit [Fintype Receiver] in
private theorem observation_submodular
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (left right : Finset Message) :
    observationEntropy code (left ∪ right) + observationEntropy code (left ∩ right) ≤
      observationEntropy code left + observationEntropy code right := by
  let distribution :=
    FiniteDistribution.uniform (Message → Fin messageLength → Alphabet)
  have h := entropy_broadcast_restrict_submodular distribution id code.encode
    (Finset.univ \ left) (Finset.univ \ right)
  have hunion :
      (Finset.univ \ left) ∪ (Finset.univ \ right) =
        Finset.univ \ (left ∩ right) := by
    ext message
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_inter]
    tauto
  have hinter :
      (Finset.univ \ left) ∩ (Finset.univ \ right) =
        Finset.univ \ (left ∪ right) := by ext; simp
  rw [hunion, hinter] at h
  simpa [observationEntropy, distribution, add_comm] using h

omit [Fintype Receiver] in
private theorem raw_submodular
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (hbroadcast : 0 < broadcastLength)
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (left right : Finset Message) :
    rawRank code (left ∪ right) + rawRank code (left ∩ right) ≤
      rawRank code left + rawRank code right := by
  have hdenom := denominator_pos (Alphabet := Alphabet)
    (broadcastLength := broadcastLength) hbroadcast
  have hobservation := observation_submodular code left right
  have hcard :
      (((left ∪ right).card : ℝ) + ((left ∩ right).card : ℝ)) =
        (left.card : ℝ) + (right.card : ℝ) := by
    exact_mod_cast Finset.card_union_add_card_inter left right
  simp only [rawRank]
  rw [← add_div, ← add_div]
  apply (div_le_div_iff_of_pos_right hdenom).2
  calc
    observationEntropy code (left ∪ right) +
          ((left ∪ right).card : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) -
          (Fintype.card Message : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) +
        (observationEntropy code (left ∩ right) +
          ((left ∩ right).card : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) -
          (Fintype.card Message : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet))) ≤
        observationEntropy code left + observationEntropy code right +
          (((left ∪ right).card : ℝ) + ((left ∩ right).card : ℝ)) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) -
          2 * (Fintype.card Message : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) := by
          linarith
    _ = observationEntropy code left + (left.card : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) -
          (Fintype.card Message : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) +
        (observationEntropy code right + (right.card : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet)) -
          (Fintype.card Message : ℝ) *
            ((messageLength : ℝ) * Real.log (Fintype.card Alphabet))) := by
          rw [hcard]
          ring

omit [Fintype Receiver] in
private theorem rawRank_monotone
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (hbroadcast : 0 < broadcastLength) (left right : Finset Message)
    (hsubset : left ⊆ right) : rawRank code left ≤ rawRank code right := by
  let distribution := FiniteDistribution.uniform
    (Message → Fin messageLength → Alphabet)
  let wordEntropy := (messageLength : ℝ) * Real.log (Fintype.card Alphabet)
  have hobservedSubset : Finset.univ \ right ⊆ Finset.univ \ left := by
    intro message hmessage
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hmessage ⊢
    exact fun hleft ↦ hmessage (hsubset hleft)
  have hconditioning := entropy_broadcast_restrict_conditioning
    distribution (fun messages ↦ messages) code.encode hobservedSubset
  have hconditioning' :
      observationEntropy code left +
          (distribution.map (restrictValues (Finset.univ \ right))).entropy ≤
        (distribution.map (restrictValues (Finset.univ \ left))).entropy +
          observationEntropy code right := by
    simpa only [observationEntropy, distribution] using hconditioning
  have hwordLog :
      Real.log (Fintype.card (Fin messageLength → Alphabet)) = wordEntropy := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [Real.log_pow]
  have hsmall := entropy_pi_restrict_uniform
    (A := Fin messageLength → Alphabet) (Finset.univ \ right)
  have hlarge := entropy_pi_restrict_uniform
    (A := Fin messageLength → Alphabet) (Finset.univ \ left)
  rw [hwordLog] at hsmall hlarge
  rw [hsmall, hlarge] at hconditioning'
  have hleftCardNat := Finset.card_sdiff_add_card (Finset.univ : Finset Message) left
  have hrightCardNat := Finset.card_sdiff_add_card (Finset.univ : Finset Message) right
  simp only [Finset.union_eq_left.mpr (Finset.subset_univ _), Finset.card_univ] at hleftCardNat
  simp only [Finset.union_eq_left.mpr (Finset.subset_univ _), Finset.card_univ] at hrightCardNat
  have hleftCard :
      (((Finset.univ \ left).card : ℝ) + (left.card : ℝ)) =
        (Fintype.card Message : ℝ) := by exact_mod_cast hleftCardNat
  have hrightCard :
      (((Finset.univ \ right).card : ℝ) + (right.card : ℝ)) =
        (Fintype.card Message : ℝ) := by exact_mod_cast hrightCardNat
  have hleftEntropy :
      ((Finset.univ \ left).card : ℝ) * wordEntropy +
          (left.card : ℝ) * wordEntropy =
        (Fintype.card Message : ℝ) * wordEntropy := by
    calc
      _ = (((Finset.univ \ left).card : ℝ) + (left.card : ℝ)) *
          wordEntropy := by ring
      _ = _ := by rw [hleftCard]
  have hrightEntropy :
      ((Finset.univ \ right).card : ℝ) * wordEntropy +
          (right.card : ℝ) * wordEntropy =
        (Fintype.card Message : ℝ) * wordEntropy := by
    calc
      _ = (((Finset.univ \ right).card : ℝ) + (right.card : ℝ)) *
          wordEntropy := by ring
      _ = _ := by rw [hrightCard]
  have hnumerator :
      observationEntropy code left + (left.card : ℝ) * wordEntropy -
          (Fintype.card Message : ℝ) * wordEntropy ≤
        observationEntropy code right + (right.card : ℝ) * wordEntropy -
          (Fintype.card Message : ℝ) * wordEntropy := by
    linarith
  have hdenominator := denominator_pos (Alphabet := Alphabet)
    (broadcastLength := broadcastLength) hbroadcast
  apply (div_le_div_iff_of_pos_right hdenominator).2
  simpa only [rawRank, wordEntropy] using hnumerator

omit [Fintype Receiver] in
private theorem rawRank_receiver
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (hzero : code.IsZeroError) (hbroadcast : 0 < broadcastLength)
    (receiver : Receiver) :
    Code.symmetricRate messageLength broadcastLength ≤
      rawRank code (insert (problem.demand receiver) (problem.interference receiver)) -
        rawRank code (problem.interference receiver) := by
  let distribution := FiniteDistribution.uniform
    (Message → Fin messageLength → Alphabet)
  have hobservation := entropy_broadcast_complement_interference_insert
    code hzero receiver distribution
  have hobservation' :
      observationEntropy code
          (insert (problem.demand receiver) (problem.interference receiver)) =
        observationEntropy code (problem.interference receiver) := by
    simpa only [observationEntropy, distribution] using hobservation
  have hcardInsert :
      ((insert (problem.demand receiver) (problem.interference receiver)).card : ℝ) =
        (problem.interference receiver).card + 1 := by
    rw [Finset.card_insert_of_notMem (demand_not_interference problem receiver)]
    norm_num
  have hbroadcastNe : (broadcastLength : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hbroadcast
  have hlogPos : 0 < Real.log (Fintype.card Alphabet) := by
    apply Real.log_pos
    exact_mod_cast Fintype.one_lt_card (α := Alphabet)
  have hlogNe : Real.log (Fintype.card Alphabet) ≠ 0 := ne_of_gt hlogPos
  apply le_of_eq
  rw [Code.symmetricRate, rawRank, rawRank, hobservation', hcardInsert]
  field_simp [hbroadcastNe, hlogNe]
  ring

private noncomputable def normalizedRank
    (raw : Finset Message → ℝ) (set : Finset Message) : ℝ :=
  raw set + (set.card : ℝ) * ((1 - raw Finset.univ) / (Fintype.card Message : ℝ))

omit [Fintype Receiver] in
private theorem normalizedRank_feasible [Nonempty Message]
    (problem : Instance Message Receiver) (rate : ℝ) (raw : Finset Message → ℝ)
    (hempty : raw ∅ = 0) (huniv : raw Finset.univ ≤ 1)
    (hmono : ∀ left right, left ⊆ right → raw left ≤ raw right)
    (hsubmod : ∀ left right,
      raw (left ∪ right) + raw (left ∩ right) ≤ raw left + raw right)
    (hreceiver : ∀ receiver,
      rate ≤ raw (insert (problem.demand receiver) (problem.interference receiver)) -
        raw (problem.interference receiver)) :
    ShannonPolymatroidFeasible problem rate (normalizedRank raw) := by
  have hcard : (Fintype.card Message : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hslack : 0 ≤ (1 - raw Finset.univ) / (Fintype.card Message : ℝ) := by
    positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [normalizedRank, hempty]
  · simp only [normalizedRank, Finset.card_univ]
    field_simp
    ring
  · intro left right hsubset
    have hcardle : (left.card : ℝ) ≤ (right.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact add_le_add (hmono left right hsubset)
      (mul_le_mul_of_nonneg_right hcardle hslack)
  · intro left right
    have hmodular :
        (((left ∪ right).card : ℝ) + ((left ∩ right).card : ℝ)) =
          (left.card : ℝ) + (right.card : ℝ) := by
      exact_mod_cast Finset.card_union_add_card_inter left right
    dsimp [normalizedRank]
    have hraw := hsubmod left right
    nlinarith
  · intro receiver
    have hcardInsert :
        ((insert (problem.demand receiver) (problem.interference receiver)).card : ℝ) =
          (problem.interference receiver).card + 1 := by
      rw [Finset.card_insert_of_notMem (demand_not_interference problem receiver)]
      norm_num
    have hraw := hreceiver receiver
    dsimp [normalizedRank]
    nlinarith

omit [Fintype Receiver] in
private theorem code_feasible
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Nontrivial Alphabet]
    [Nonempty Message]
    {problem : Instance Message Receiver} {messageLength broadcastLength : ℕ}
    (code : Code problem Alphabet Alphabet messageLength broadcastLength)
    (hzero : code.IsZeroError) (hbroadcast : 0 < broadcastLength) :
    ∃ rank, ShannonPolymatroidFeasible problem
      (Code.symmetricRate messageLength broadcastLength) rank := by
  let raw := rawRank code
  exact ⟨normalizedRank raw,
    normalizedRank_feasible problem _ raw
      (raw_empty code)
      (raw_univ_le_one hbroadcast code)
      (fun left right hsubset ↦ rawRank_monotone code hbroadcast left right hsubset)
      (fun left right ↦ raw_submodular hbroadcast code left right)
      (fun receiver ↦ rawRank_receiver code hzero hbroadcast receiver)⟩

end ShannonCertificate

/-- Best symmetric outer-bound value obtainable from Shannon polymatroid constraints. -/
@[capacity_shared_api]
noncomputable def shannonPolymatroidOuterBound (problem : Instance Message Receiver) : ℝ :=
  sSup {rate | ∃ rank, ShannonPolymatroidFeasible problem rate rank}

omit [Fintype Receiver] in
private theorem shannonPolymatroidFeasible_rate_le_one [Nonempty Receiver]
    (problem : Instance Message Receiver) {rate : ℝ} {rank : Finset Message → ℝ}
    (hfeasible : ShannonPolymatroidFeasible problem rate rank) : rate ≤ 1 := by
  let receiver : Receiver := Classical.choice (inferInstance : Nonempty Receiver)
  have hnonnegative : 0 ≤ rank (problem.interference receiver) := by
    rw [← hfeasible.1]
    exact hfeasible.2.2.1 ∅ _ (Finset.empty_subset _)
  have hbounded :
      rank (insert (problem.demand receiver) (problem.interference receiver)) ≤ 1 := by
    rw [← hfeasible.2.1]
    exact hfeasible.2.2.1 _ Finset.univ (Finset.subset_univ _)
  linarith [hfeasible.2.2.2.2 receiver]

omit [Fintype Receiver] in
private theorem shannonPolymatroidRates_bounded [Nonempty Receiver]
    (problem : Instance Message Receiver) :
    BddAbove {rate | ∃ rank, ShannonPolymatroidFeasible problem rate rank} := by
  refine ⟨1, ?_⟩
  rintro rate ⟨rank, hfeasible⟩
  exact shannonPolymatroidFeasible_rate_le_one problem hfeasible

omit [Fintype Message] [Fintype Receiver] in
private theorem zeroRate_achievable (problem : Instance Message Receiver) :
    AchievableSymmetricRate problem 0 := by
  refine ⟨2, by norm_num, ?_⟩
  intro δ hδ firstBroadcastLength
  let code : Code problem (Fin 2) (Fin 2) 0 (firstBroadcastLength + 1) :=
    { encode := fun _ _ ↦ 0
      decode := fun _ _ _ coordinate ↦ Fin.elim0 coordinate }
  exact ⟨0, firstBroadcastLength + 1, Nat.le_add_right _ _, Nat.zero_lt_succ _, code,
    (by intro _ _ coordinate; exact Fin.elim0 coordinate),
    by simp [Code.symmetricRate, hδ.le]⟩

omit [Fintype Receiver] in
private theorem achievableSymmetricRate_le_shannonPolymatroidOuterBound
    [Nonempty Receiver] (problem : Instance Message Receiver)
    {rate : ℝ} (hrate : AchievableSymmetricRate problem rate) :
    rate ≤ shannonPolymatroidOuterBound problem := by
  let receiver : Receiver := Classical.choice (inferInstance : Nonempty Receiver)
  letI : Nonempty Message := ⟨problem.demand receiver⟩
  rcases hrate with ⟨alphabetCard, halphabetCard, hrate⟩
  letI : Nontrivial (Fin alphabetCard) := Fin.nontrivial_iff_two_le.mpr halphabetCard
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨messageLength, broadcastLength, _, hbroadcast, code, hzero, hclose⟩ :=
    hrate δ hδ 0
  have hcode : Code.symmetricRate messageLength broadcastLength ≤
      shannonPolymatroidOuterBound problem := by
    unfold shannonPolymatroidOuterBound
    apply le_csSup (shannonPolymatroidRates_bounded problem)
    exact ShannonCertificate.code_feasible code hzero hbroadcast
  linarith

/- Every operationally achievable symmetric rate satisfies the Shannon polymatroid bound. -/
omit [Fintype Receiver] in
theorem symmetricCapacity_le_shannonPolymatroidOuterBound [Nonempty Receiver]
    (problem : Instance Message Receiver) :
    symmetricCapacity problem ≤ shannonPolymatroidOuterBound problem := by
  unfold symmetricCapacity
  apply csSup_le
  · exact ⟨0, zeroRate_achievable problem⟩
  · intro rate hrate
    exact achievableSymmetricRate_le_shannonPolymatroidOuterBound problem hrate

attribute [capacity_shared_api] symmetricCapacity_le_shannonPolymatroidOuterBound

end CapacityAtlas.IndexCoding
