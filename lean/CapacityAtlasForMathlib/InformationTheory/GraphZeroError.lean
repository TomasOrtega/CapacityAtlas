/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CapacityAtlas

def IsGraphZeroErrorCode {Vertex : Type*} [DecidableEq Vertex]
    (adjacent : Vertex → Vertex → Prop) [DecidableRel adjacent]
    (blocklength : ℕ) (code : Finset (Fin blocklength → Vertex)) : Prop :=
  ∀ left ∈ code, ∀ right ∈ code, left ≠ right →
    ∃ coordinate, left coordinate ≠ right coordinate ∧
      ¬adjacent (left coordinate) (right coordinate)

noncomputable def graphShannonCapacity {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (adjacent : Vertex → Vertex → Prop) [DecidableRel adjacent] : ℝ :=
  sSup {rate | ∃ blocklength : ℕ, ∃ code : Finset (Fin blocklength → Vertex),
    0 < blocklength ∧ IsGraphZeroErrorCode adjacent blocklength code ∧
      rate = Real.rpow code.card ((blocklength : ℝ)⁻¹)}

end CapacityAtlas
