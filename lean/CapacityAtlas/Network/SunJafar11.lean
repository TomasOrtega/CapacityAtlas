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
def sunJafar11ExpectedInternalConflicts : Finset SunJafar11Edge :=
  {(0, 3), (0, 4), (1, 4), (1, 5), (2, 5)}

private theorem sunJafar11_interference_member_lt_six
    (receiver : SunJafar11Receiver) (message : SunJafar11Message)
    (h : message ∈ sunJafar11.interference receiver) : message.val < 6 := by
  rw [sunJafar11_interference] at h
  fin_cases receiver <;> simp [sunJafar11Interference] at h
  all_goals first
    | subst message; decide
    | rcases h with h | h <;> subst message <;> decide

private theorem sunJafar11_alignment_adj_endpoints_lt_six
    {left right : SunJafar11Message}
    (h : (alignmentGraph sunJafar11).Adj left right) :
    left.val < 6 ∧ right.val < 6 := by
  rw [alignmentGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨_, receiver, hleft, hright⟩ | ⟨_, receiver, hright, hleft⟩
  all_goals exact ⟨sunJafar11_interference_member_lt_six receiver left hleft,
    sunJafar11_interference_member_lt_six receiver right hright⟩

private theorem sunJafar11_reachable_two_of_lt_six
    (message : SunJafar11Message) (hmessage : message.val < 6) :
    (alignmentGraph sunJafar11).Reachable message 2 := by
  fin_cases message
  · exact (by native_decide : (alignmentGraph sunJafar11).Adj 0 2).reachable
  · exact (by native_decide : (alignmentGraph sunJafar11).Adj 1 2).reachable
  · exact .refl _
  · exact (by native_decide : (alignmentGraph sunJafar11).Adj 3 2).reachable
  · exact (by native_decide : (alignmentGraph sunJafar11).Adj 4 2).reachable
  · exact ((by native_decide : (alignmentGraph sunJafar11).Adj 5 3).reachable).trans
      (by native_decide : (alignmentGraph sunJafar11).Adj 3 2).reachable
  all_goals simp at hmessage

theorem sunJafar11_alignment_reachable_iff (left right : SunJafar11Message) :
    (alignmentGraph sunJafar11).Reachable left right ↔
      (left.val < 6 ∧ right.val < 6) ∨ left = right := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h using Relation.ReflTransGen.trans_induction_on with
    | refl vertex => exact Or.inr rfl
    | single hadj => exact Or.inl (sunJafar11_alignment_adj_endpoints_lt_six hadj)
    | trans _ _ ihleft ihrigth =>
        rcases ihleft with hleft | rfl
        · rcases ihrigth with hright | rfl
          · exact Or.inl ⟨hleft.1, hright.2⟩
          · exact Or.inl hleft
        · exact ihrigth
  · rintro (h | rfl)
    · exact (sunJafar11_reachable_two_of_lt_six left h.1).trans
        (sunJafar11_reachable_two_of_lt_six right h.2).symm
    · exact .refl _

/-- The listed pairs are exactly the internal conflicts, with endpoints ordered. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_internalConflicts_exact :
    {edge : SunJafar11Edge |
      edge.1 < edge.2 ∧ IsInternalConflict sunJafar11 edge.1 edge.2} =
      ↑sunJafar11ExpectedInternalConflicts := by
  ext edge
  rcases edge with ⟨left, right⟩
  simp only [Set.mem_setOf_eq, Finset.mem_coe, IsInternalConflict]
  rw [sunJafar11_alignment_reachable_iff]
  fin_cases left <;> fin_cases right <;> native_decide

def sunJafar11AreAligned (left right : SunJafar11Message) : Bool :=
  decide ((left, right) ∈ sunJafar11AlignmentEdges ∨
    (right, left) ∈ sunJafar11AlignmentEdges)

def sunJafar11HasAlignmentPathTwo (left right : SunJafar11Message) : Bool :=
  decide ((Finset.univ.filter fun middle ↦
    sunJafar11AreAligned left middle && sunJafar11AreAligned middle right).Nonempty)

/-- Every listed internal conflict has alignment-graph distance exactly two. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_internalConflictDistance_two :
    sunJafar11ExpectedInternalConflicts.filter (fun edge ↦
      !sunJafar11AreAligned edge.1 edge.2 &&
        sunJafar11HasAlignmentPathTwo edge.1 edge.2) =
      sunJafar11ExpectedInternalConflicts := by
  native_decide

/-- The published construction has a linear encoder and achieves symmetric rate `5/13`. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_linear_achievability : Prop :=
  (5 : ℝ) / 13 ≤ linearEncoderSymmetricCapacity sunJafar11

/-- The published code gives the same lower bound without a linearity restriction. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_unrestricted_achievability : Prop :=
  (5 : ℝ) / 13 ≤ symmetricCapacity sunJafar11

/-- Linear-encoder achievability implies unrestricted achievability. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_linear_achievability_implies_unrestricted_achievability
    (h : sunJafar11_linear_achievability) : sunJafar11_unrestricted_achievability := by
  exact h.trans (linearEncoderSymmetricCapacity_le_symmetricCapacity sunJafar11)

/-- No zero-error code with a linear encoder exceeds symmetric rate `5/13`. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_linear_converse : Prop :=
  linearEncoderSymmetricCapacity sunJafar11 ≤ (5 : ℝ) / 13

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

/-- The operational symmetric capacity is at most the Shannon relaxation value `2/5`. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_statement]
def sunJafar11_shannon_outer_bound : Prop :=
  symmetricCapacity sunJafar11 ≤ (2 : ℝ) / 5

/-- The computed Shannon relaxation value implies the operational outer bound. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_short_proof]
theorem sunJafar11_shannon_relaxation_value_implies_outer_bound
    (h : sunJafar11_shannon_outer_bound_limit) : sunJafar11_shannon_outer_bound := by
  exact (symmetricCapacity_le_shannonPolymatroidOuterBound sunJafar11).trans_eq h

end CapacityAtlas.IndexCoding
