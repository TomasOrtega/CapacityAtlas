/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteStateChannel
import CapacityAtlasForMathlib.InformationTheory.OperationalTheory
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace CapacityAtlas.Channel

open CapacityAtlas

noncomputable def trapdoorTransition : Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => 1
  | true, true, true, true => 1
  | false, true, false, true => 1 / 2
  | false, true, true, false => 1 / 2
  | true, false, true, false => 1 / 2
  | true, false, false, true => 1 / 2
  | _, _, _, _ => 0

/-- The binary trapdoor channel: one of the stored and inserted bits leaves uniformly. -/
noncomputable def trapdoorChannel : FiniteStateChannel Bool Bool Bool where
  transition := trapdoorTransition
  nonnegative input state output nextState := by
    cases input <;> cases state <;> cases output <;> cases nextState <;>
      norm_num [trapdoorTransition]
  row_sum input state := by
    cases input <;> cases state <;> norm_num [trapdoorTransition, Fintype.sum_bool]

@[capacity_problem "trapdoor-channel-with-feedback", capacity_definition]
noncomputable def trapdoorFeedbackModel : FiniteStateChannel Bool Bool Bool :=
  trapdoorChannel

@[capacity_problem "trapdoor-channel-without-feedback", capacity_definition]
noncomputable def trapdoorFeedforwardModel : FiniteStateChannel Bool Bool Bool :=
  trapdoorChannel

/-- Feedback permits causal dependence on past outputs; the initial state is fixed and known. -/
@[capacity_problem "trapdoor-channel-with-feedback", capacity_statement]
def trapdoorFeedbackCapacityStatement
  (feedbackTheory : ScalarOperationalTheory (FiniteStateChannel Bool Bool Bool)) : Prop :=
  feedbackTheory.capacity trapdoorFeedbackModel =
    Real.log ((1 + Real.sqrt 5) / 2) / Real.log 2

/-- Feedforward capacity remains distinct from the solved feedback quantity. -/
@[capacity_problem "trapdoor-channel-without-feedback", capacity_statement]
def trapdoorWithoutFeedbackCapacityBounds
  (feedforwardTheory : ScalarOperationalTheory (FiniteStateChannel Bool Bool Bool)) : Prop :=
  0 ≤ feedforwardTheory.capacity trapdoorFeedforwardModel ∧
    feedforwardTheory.capacity trapdoorFeedforwardModel ≤ 1

end CapacityAtlas.Channel
