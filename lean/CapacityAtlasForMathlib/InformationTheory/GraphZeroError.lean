/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CapacityAtlas

/-- Every pair of distinct codewords has a coordinate with distinct, nonadjacent vertices. -/
def IsGraphZeroErrorCode {Vertex : Type*} [DecidableEq Vertex]
    (adjacent : Vertex → Vertex → Prop) [DecidableRel adjacent]
    (blocklength : ℕ) (code : Finset (Fin blocklength → Vertex)) : Prop :=
  ∀ left ∈ code, ∀ right ∈ code, left ≠ right →
    ∃ coordinate, left coordinate ≠ right coordinate ∧
      ¬adjacent (left coordinate) (right coordinate)

/-- Supremum of zero-error graph code sizes raised to the inverse positive blocklength. -/
noncomputable def graphShannonCapacity {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (adjacent : Vertex → Vertex → Prop) [DecidableRel adjacent] : ℝ :=
  sSup {rate | ∃ blocklength : ℕ, ∃ code : Finset (Fin blocklength → Vertex),
    0 < blocklength ∧ IsGraphZeroErrorCode adjacent blocklength code ∧
      rate = Real.rpow code.card ((blocklength : ℝ)⁻¹)}

end CapacityAtlas
