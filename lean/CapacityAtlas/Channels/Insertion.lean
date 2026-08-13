/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.VariableLengthChannel

open scoped BigOperators

namespace CapacityAtlas.Channel

open CapacityAtlas

/-- After each transmitted bit, independently insert one fair bit with probability `p`. -/
@[capacity_problem "binary-insertion-channel", capacity_definition]
noncomputable def randomBinaryInsertionStep (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    VariableLengthChannelStep Bool Bool where
  support input := {[input], [input, false], [input, true]}
  transition input output :=
    if output = [input] then 1 - p
    else if output = [input, false] ∨ output = [input, true] then p / 2
    else 0
  nonnegative input output := by
    split
    · linarith
    · split <;> positivity
  row_sum input := by
    cases input <;> simp
  zero_outside input output hout := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
    rcases hout with ⟨hword, hfalse, htrue⟩
    simp [hword, hfalse, htrue]

end CapacityAtlas.Channel
