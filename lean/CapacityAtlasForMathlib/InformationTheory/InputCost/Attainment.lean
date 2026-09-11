/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0

Adapted from TomasOrtega/CapacityAtlasInputCost, commit 5e6a432bc276aa4e08b7f27658daf40e029cda48,
CapacityAtlasCost/Attainment.lean. Imports and certificate types use the monorepo modules.
-/

import CapacityAtlasForMathlib.InformationTheory.InputCost.Converse
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

open scoped BigOperators

namespace CapacityAtlas.FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem exists_admissible_input_attaining_constrainedInformationCapacityBits
    (channel : FiniteChannel X Y) (cost : X → ℝ) (budget : ℝ)
    (hfeasible : ∃ symbol, cost symbol ≤ budget) :
    ∃ input : FiniteDistribution X, input.IsAdmissibleCost cost budget ∧
      channel.mutualInformationBits input =
        channel.constrainedInformationCapacityBits cost budget := by
  classical
  let feasible : Set (X → ℝ) :=
    stdSimplex ℝ X ∩ {p | ∑ x, p x * cost x ≤ budget}
  have hcompact : IsCompact feasible :=
    (isCompact_stdSimplex ℝ X).inter_right (isClosed_le (by fun_prop) continuous_const)
  have hnonempty : feasible.Nonempty := by
    obtain ⟨symbol, hsymbol⟩ := hfeasible
    let point := inputCostPointMass symbol
    refine ⟨point, ⟨point.nonnegative, point.sum_probability⟩, ?_⟩
    change point.expectedCost cost ≤ budget
    simpa [point, inputCostPointMass_expectedCost] using hsymbol
  let information : (X → ℝ) → ℝ := fun p ↦
    ((∑ y, Real.negMulLog (∑ x, p x * channel.transition x y)) -
      ∑ x, p x * (channel.rowDistribution x).entropy) / Real.log 2
  have hcontinuous : Continuous information := by
    dsimp [information]
    fun_prop
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hnonempty hcontinuous.continuousOn
  let input : FiniteDistribution X := ⟨p, hp.1.1, hp.1.2⟩
  have hadmissible : input.IsAdmissibleCost cost budget := hp.2
  refine ⟨input, hadmissible, le_antisymm
    (channel.mutualInformationBits_le_constrainedInformationCapacityBits input hadmissible) ?_⟩
  apply csSup_le (channel.constrainedInformationValues_nonempty cost budget hfeasible)
  rintro value ⟨other, hother, rfl⟩
  exact hmax ⟨⟨other.nonnegative, other.sum_probability⟩, hother⟩

end CapacityAtlas.FiniteChannel
