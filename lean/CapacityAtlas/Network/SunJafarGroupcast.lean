/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.IndexCoding

namespace CapacityAtlas.IndexCoding

abbrev SunJafarGroupcastMessage := Fin 6
abbrev SunJafarGroupcastReceiver := Fin 10
abbrev SunJafarGroupcastEdge := SunJafarGroupcastMessage × SunJafarGroupcastMessage

/-- Demands in the paper's one-based receiver order. -/
@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_definition]
def sunJafarGroupcastDemandOneBased : SunJafarGroupcastReceiver → ℕ :=
  ![1, 1, 2, 3, 4, 5, 6, 6, 6, 6]

/-- Interference rows in the paper's one-based message labels. -/
@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_definition]
def sunJafarGroupcastInterferenceOneBased :
    SunJafarGroupcastReceiver → Finset ℕ :=
  ![
    {2, 4},
    {4, 5},
    {5},
    ∅,
    ∅,
    {2},
    {1, 3},
    {2, 3},
    {3, 4},
    {3, 5}
  ]

def sunJafarGroupcastDemand :
    SunJafarGroupcastReceiver → SunJafarGroupcastMessage :=
  ![0, 0, 1, 2, 3, 4, 5, 5, 5, 5]

def sunJafarGroupcastInterference :
    SunJafarGroupcastReceiver → Finset SunJafarGroupcastMessage :=
  ![
    {1, 3},
    {3, 4},
    {4},
    ∅,
    ∅,
    {1},
    {0, 2},
    {1, 2},
    {2, 3},
    {2, 4}
  ]

/-- The six-message, ten-receiver groupcast instance in Sun--Jafar. -/
@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_definition]
def sunJafarGroupcast :
    Instance SunJafarGroupcastMessage SunJafarGroupcastReceiver :=
  Instance.fromInterference sunJafarGroupcastDemand sunJafarGroupcastInterference

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_short_proof]
theorem sunJafarGroupcast_demand_translation (receiver : SunJafarGroupcastReceiver) :
    (sunJafarGroupcastDemand receiver).val + 1 =
      sunJafarGroupcastDemandOneBased receiver := by
  fin_cases receiver <;> native_decide

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_short_proof]
theorem sunJafarGroupcast_interference_translation (receiver : SunJafarGroupcastReceiver) :
    (sunJafarGroupcastInterference receiver).image (fun message ↦ message.val + 1) =
      sunJafarGroupcastInterferenceOneBased receiver := by
  fin_cases receiver <;> native_decide

@[simp] theorem sunJafarGroupcast_interference (receiver : SunJafarGroupcastReceiver) :
    sunJafarGroupcast.interference receiver = sunJafarGroupcastInterference receiver := by
  apply Instance.interference_fromInterference
  intro sourceReceiver
  fin_cases sourceReceiver <;>
    simp [sunJafarGroupcastDemand, sunJafarGroupcastInterference]

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_definition]
def sunJafarGroupcastAlignmentEdges : Finset SunJafarGroupcastEdge :=
  Finset.univ.filter fun edge ↦
    edge.1 < edge.2 ∧ ∃ receiver,
      edge.1 ∈ sunJafarGroupcastInterference receiver ∧
        edge.2 ∈ sunJafarGroupcastInterference receiver

def sunJafarGroupcastExpectedAlignmentEdges : Finset SunJafarGroupcastEdge :=
  {(0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4)}

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_short_proof]
theorem sunJafarGroupcast_alignmentEdges_exact :
    sunJafarGroupcastAlignmentEdges = sunJafarGroupcastExpectedAlignmentEdges := by
  native_decide

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_short_proof]
theorem sunJafarGroupcast_alignmentEdge_count :
    sunJafarGroupcastAlignmentEdges.card = 6 := by
  native_decide

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_statement]
def sunJafarGroupcast_linear_achievability : Prop :=
  (5 : ℝ) / 13 ≤ symmetricCapacity sunJafarGroupcast

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_statement]
def sunJafarGroupcast_linear_converse : Prop :=
  linearSymmetricCapacity sunJafarGroupcast ≤ (5 : ℝ) / 13

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_statement]
def sunJafarGroupcast_nonlinear_converse : Prop :=
  symmetricCapacity sunJafarGroupcast ≤ (11 : ℝ) / 28

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_statement]
def sunJafarGroupcast_exact_capacity_conjecture : Prop :=
  symmetricCapacity sunJafarGroupcast = (5 : ℝ) / 13

@[capacity_problem "sun-jafar-six-message-groupcast-index-coding", capacity_statement]
def sunJafarGroupcast_shannon_outer_bound_limit : Prop :=
  shannonPolymatroidOuterBound sunJafarGroupcast = (2 : ℝ) / 5

end CapacityAtlas.IndexCoding
