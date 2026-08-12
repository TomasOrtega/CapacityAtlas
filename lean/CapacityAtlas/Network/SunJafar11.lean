/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.IndexCoding

namespace CapacityAtlas.IndexCoding

abbrev SunJafar11Message := Fin 11
abbrev SunJafar11Receiver := Fin 11
abbrev SunJafar11Edge := SunJafar11Message × SunJafar11Message

/-- The source table, retaining the paper's one-based message labels. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_definition]
def sunJafar11InterferenceOneBased : SunJafar11Receiver → Finset ℕ :=
  ![
    {4, 5},
    {5},
    ∅,
    ∅,
    {2},
    {2, 3},
    {1, 3},
    {2, 4},
    {3, 4},
    {3, 5},
    {4, 6}
  ]

/-- The source table translated to Lean's zero-based `Fin 11`. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_definition]
def sunJafar11Interference : SunJafar11Receiver → Finset SunJafar11Message :=
  ![
    {3, 4},
    {4},
    ∅,
    ∅,
    {1},
    {1, 2},
    {0, 2},
    {1, 3},
    {2, 3},
    {2, 4},
    {3, 5}
  ]

/-- The exact 11-message multiple-unicast instance studied by Sun and Jafar. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_definition]
def sunJafar11 : Instance SunJafar11Message SunJafar11Receiver :=
  Instance.fromInterference id sunJafar11Interference

/-- The checked one-based translation of all eleven source rows. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_oneBased_translation (receiver : SunJafar11Receiver) :
    (sunJafar11Interference receiver).image (fun message ↦ message.val + 1) =
      sunJafar11InterferenceOneBased receiver := by
  fin_cases receiver <;>
    native_decide

@[simp] theorem sunJafar11_receiver1 : sunJafar11Interference 0 = {3, 4} := rfl
@[simp] theorem sunJafar11_receiver2 : sunJafar11Interference 1 = {4} := rfl
@[simp] theorem sunJafar11_receiver3 : sunJafar11Interference 2 = ∅ := rfl
@[simp] theorem sunJafar11_receiver4 : sunJafar11Interference 3 = ∅ := rfl
@[simp] theorem sunJafar11_receiver5 : sunJafar11Interference 4 = {1} := rfl
@[simp] theorem sunJafar11_receiver6 : sunJafar11Interference 5 = {1, 2} := rfl
@[simp] theorem sunJafar11_receiver7 : sunJafar11Interference 6 = {0, 2} := rfl
@[simp] theorem sunJafar11_receiver8 : sunJafar11Interference 7 = {1, 3} := rfl
@[simp] theorem sunJafar11_receiver9 : sunJafar11Interference 8 = {2, 3} := rfl
@[simp] theorem sunJafar11_receiver10 : sunJafar11Interference 9 = {2, 4} := rfl
@[simp] theorem sunJafar11_receiver11 : sunJafar11Interference 10 = {3, 5} := rfl

/-- The operational side-information table is exactly the complement of the source table. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_sideInformation_complement (receiver : SunJafar11Receiver) :
    sunJafar11.sideInformation receiver =
      (Finset.univ.erase (sunJafar11.demand receiver)) \
        sunJafar11Interference receiver :=
  rfl

@[simp] theorem sunJafar11_demand (receiver : SunJafar11Receiver) :
    sunJafar11.demand receiver = receiver :=
  rfl

@[simp] theorem sunJafar11_interference (receiver : SunJafar11Receiver) :
    sunJafar11.interference receiver = sunJafar11Interference receiver := by
  apply Instance.interference_fromInterference
  intro sourceReceiver
  fin_cases sourceReceiver <;> simp [sunJafar11Interference]

/-- Alignment edges derived from pairs that interfere at a common receiver. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_definition]
def sunJafar11AlignmentEdges : Finset SunJafar11Edge :=
  Finset.univ.filter fun edge ↦
    edge.1 < edge.2 ∧ ∃ receiver,
      edge.1 ∈ sunJafar11Interference receiver ∧
        edge.2 ∈ sunJafar11Interference receiver

def sunJafar11ExpectedAlignmentEdges : Finset SunJafar11Edge :=
  {(0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (3, 5)}

@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_alignmentEdges_exact :
    sunJafar11AlignmentEdges = sunJafar11ExpectedAlignmentEdges := by
  native_decide

@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_alignmentEdge_count : sunJafar11AlignmentEdges.card = 7 := by
  native_decide

@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_atMostTwoInterferers (receiver : SunJafar11Receiver) :
    (sunJafar11Interference receiver).card ≤ 2 := by
  fin_cases receiver <;> native_decide

def sunJafar11InnerDiamond : Finset SunJafar11Message := {1, 2, 3, 4}

def sunJafar11ExpectedDiamondEdges : Finset SunJafar11Edge :=
  {(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)}

@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_innerDiamond_exact :
    sunJafar11AlignmentEdges.filter
        (fun edge ↦ edge.1 ∈ sunJafar11InnerDiamond ∧ edge.2 ∈ sunJafar11InnerDiamond) =
      sunJafar11ExpectedDiamondEdges := by
  native_decide

/-- Internal conflict pairs shown in the source alignment/conflict graph. -/
def sunJafar11InternalConflicts : Finset SunJafar11Edge :=
  {(0, 3), (0, 4), (1, 4), (1, 5), (2, 5)}

def sunJafar11IsConflict (left right : SunJafar11Message) : Bool :=
  decide (right ∈ sunJafar11Interference left ∨ left ∈ sunJafar11Interference right)

def sunJafar11AreAligned (left right : SunJafar11Message) : Bool :=
  decide ((left, right) ∈ sunJafar11AlignmentEdges ∨
    (right, left) ∈ sunJafar11AlignmentEdges)

def sunJafar11HasAlignmentPathTwo (left right : SunJafar11Message) : Bool :=
  decide ((Finset.univ.filter fun middle ↦
    sunJafar11AreAligned left middle && sunJafar11AreAligned middle right).Nonempty)

@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_internalConflicts_present :
    sunJafar11InternalConflicts.filter
        (fun edge ↦ sunJafar11IsConflict edge.1 edge.2) =
      sunJafar11InternalConflicts := by
  native_decide

/-- Every listed internal conflict has alignment-graph distance exactly two. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_internalConflictDistance_two :
    sunJafar11InternalConflicts.filter (fun edge ↦
      !sunJafar11AreAligned edge.1 edge.2 &&
        sunJafar11HasAlignmentPathTwo edge.1 edge.2) =
      sunJafar11InternalConflicts := by
  native_decide

/-- The published vector-linear code is also a nonlinear zero-error achievability claim. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_linear_achievability : Prop :=
  (5 : ℝ) / 13 ≤ symmetricCapacity sunJafar11

/-- No vector-linear code over any finite field exceeds symmetric rate `5/13`. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_linear_converse : Prop :=
  linearSymmetricCapacity sunJafar11 ≤ (5 : ℝ) / 13

/-- The Zhang--Yeung converse for unrestricted nonlinear zero-error codes. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_nonlinear_converse : Prop :=
  symmetricCapacity sunJafar11 ≤ (11 : ℝ) / 28

/-- The open exact nonlinear symmetric-capacity claim. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_exact_capacity_conjecture : Prop :=
  symmetricCapacity sunJafar11 = (5 : ℝ) / 13

/-- Shannon polymatroid inequalities alone stop at the outer value `2/5`. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_shannon_outer_bound_limit : Prop :=
  shannonPolymatroidOuterBound sunJafar11 = (2 : ℝ) / 5

end CapacityAtlas.IndexCoding
