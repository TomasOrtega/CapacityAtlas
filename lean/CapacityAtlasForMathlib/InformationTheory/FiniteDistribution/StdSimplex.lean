/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution
import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-! Equivalence and pushforward compatibility with finitely supported real simplices. -/

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {X Y : Type*} [Fintype X]

/-- Regard a finite distribution as mathlib's finitely supported real simplex. -/
@[capacity_shared_api]
noncomputable def toStdSimplex (distribution : FiniteDistribution X) :
    Convexity.StdSimplex ℝ X where
  weights := Finsupp.equivFunOnFinite.symm distribution
  nonneg := distribution.nonnegative
  total := by
    rw [Finsupp.equivFunOnFinite_symm_sum]
    exact distribution.sum_probability

@[simp, capacity_shared_api]
theorem toStdSimplex_weights_apply (distribution : FiniteDistribution X) (x : X) :
    distribution.toStdSimplex.weights x = distribution x :=
  rfl

/-- Regard a real simplex on a finite type as an atlas distribution. -/
@[capacity_shared_api]
def ofStdSimplex (distribution : Convexity.StdSimplex ℝ X) : FiniteDistribution X where
  probability := distribution.weights
  nonnegative := distribution.weights_nonneg
  sum_probability :=
    (Finsupp.sum_fintype distribution.weights (fun _ r ↦ r) (fun _ ↦ rfl)).symm.trans
      distribution.total

@[simp, capacity_shared_api]
theorem ofStdSimplex_apply (distribution : Convexity.StdSimplex ℝ X) (x : X) :
    ofStdSimplex distribution x = distribution.weights x :=
  rfl

@[simp, capacity_shared_api]
theorem ofStdSimplex_toStdSimplex (distribution : FiniteDistribution X) :
    ofStdSimplex distribution.toStdSimplex = distribution := by
  ext x
  rfl

@[simp, capacity_shared_api]
theorem toStdSimplex_ofStdSimplex (distribution : Convexity.StdSimplex ℝ X) :
    (ofStdSimplex distribution).toStdSimplex = distribution := by
  ext x
  rfl

/-- On finite types, atlas distributions and mathlib real simplices contain the same data. -/
@[capacity_shared_api]
noncomputable def equivStdSimplex : FiniteDistribution X ≃ Convexity.StdSimplex ℝ X where
  toFun := toStdSimplex
  invFun := ofStdSimplex
  left_inv := ofStdSimplex_toStdSimplex
  right_inv := toStdSimplex_ofStdSimplex

/-- Push a finite distribution into any target type using mathlib's simplex pushforward. -/
@[capacity_shared_api]
noncomputable def mapStdSimplex (distribution : FiniteDistribution X) (f : X → Y) :
    Convexity.StdSimplex ℝ Y :=
  distribution.toStdSimplex.map f

@[capacity_shared_api]
theorem mapStdSimplex_weights_apply [DecidableEq Y]
    (distribution : FiniteDistribution X) (f : X → Y) (y : Y) :
    (distribution.mapStdSimplex f).weights y = ∑ x with f x = y, distribution x := by
  classical
  simp only [mapStdSimplex, Convexity.StdSimplex.weights_map, Finsupp.mapDomain,
    Finsupp.sum_apply, Finsupp.single_apply]
  rw [Finsupp.sum_fintype _ (fun x r ↦ if f x = y then r else 0) (by simp)]
  simp only [toStdSimplex_weights_apply, Finset.sum_filter]

@[simp, capacity_shared_api]
theorem toStdSimplex_map [Fintype Y] [DecidableEq Y]
    (distribution : FiniteDistribution X) (f : X → Y) :
    (distribution.map f).toStdSimplex = distribution.toStdSimplex.map f := by
  ext y
  exact (distribution.mapStdSimplex_weights_apply f y).symm

@[simp, capacity_shared_api]
theorem ofStdSimplex_map [Fintype Y] [DecidableEq Y]
    (distribution : Convexity.StdSimplex ℝ X) (f : X → Y) :
    ofStdSimplex (distribution.map f) = (ofStdSimplex distribution).map f := by
  simpa only [ofStdSimplex_toStdSimplex, toStdSimplex_ofStdSimplex] using
    (congrArg ofStdSimplex ((ofStdSimplex distribution).toStdSimplex_map f)).symm

end CapacityAtlas.FiniteDistribution
