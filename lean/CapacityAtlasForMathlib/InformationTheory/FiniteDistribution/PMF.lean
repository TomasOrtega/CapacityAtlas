/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The same finite distribution as a mathlib probability mass function. -/
@[capacity_shared_api]
noncomputable def toPMF (distribution : FiniteDistribution X) : PMF X :=
  PMF.ofFintype (fun x ↦ ENNReal.ofReal (distribution x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun x ↦ distribution x) (fun x _ ↦ distribution.nonnegative x)]
    simp)

@[simp, capacity_shared_api]
theorem toPMF_apply (distribution : FiniteDistribution X) (x : X) :
    distribution.toPMF x = ENNReal.ofReal (distribution x) := rfl

@[simp, capacity_shared_api]
theorem toPMF_apply_toReal (distribution : FiniteDistribution X) (x : X) :
    (distribution.toPMF x).toReal = distribution x :=
  ENNReal.toReal_ofReal (distribution.nonnegative x)

/-- A mathlib probability mass function on a finite alphabet, with real weights. -/
@[capacity_shared_api]
noncomputable def ofPMF (distribution : PMF X) : FiniteDistribution X where
  probability x := (distribution x).toReal
  nonnegative _ := ENNReal.toReal_nonneg
  sum_probability := by
    have hsum : ∑ x, distribution x = 1 := by
      simpa only [tsum_fintype] using distribution.tsum_coe
    rw [← ENNReal.toReal_sum (fun x _ ↦ distribution.apply_ne_top x),
      hsum, ENNReal.toReal_one]

@[simp, capacity_shared_api]
theorem ofPMF_apply (distribution : PMF X) (x : X) :
    ofPMF distribution x = (distribution x).toReal := rfl

@[simp, capacity_shared_api]
theorem ofPMF_toPMF (distribution : FiniteDistribution X) :
    ofPMF distribution.toPMF = distribution := by
  ext x
  exact distribution.toPMF_apply_toReal x

@[simp, capacity_shared_api]
theorem toPMF_ofPMF (distribution : PMF X) :
    (ofPMF distribution).toPMF = distribution := by
  ext x
  exact ENNReal.ofReal_toReal (distribution.apply_ne_top x)

/-- Finite real distributions and mathlib PMFs carry the same data. -/
@[capacity_shared_api]
noncomputable def equivPMF (X : Type*) [Fintype X] : FiniteDistribution X ≃ PMF X where
  toFun := toPMF
  invFun := ofPMF
  left_inv := ofPMF_toPMF
  right_inv := toPMF_ofPMF

@[simp, capacity_shared_api]
theorem toPMF_map [DecidableEq Y] (distribution : FiniteDistribution X) (f : X → Y) :
    (distribution.map f).toPMF = distribution.toPMF.map f := by
  classical
  ext y
  rw [toPMF_apply, PMF.map_apply, tsum_fintype]
  change ENNReal.ofReal (∑ x with f x = y, distribution x) = _
  rw [ENNReal.ofReal_sum_of_nonneg (f := fun x ↦ distribution x)
    (fun x _ ↦ distribution.nonnegative x)]
  simp only [Finset.sum_filter, toPMF_apply, eq_comm]

/-- The finite entropy formula agrees with the real masses of its PMF. -/
@[capacity_shared_api]
theorem entropy_eq_sum_toPMF (distribution : FiniteDistribution X) :
    distribution.entropy = ∑ x, Real.negMulLog (distribution.toPMF x).toReal := by
  simp [entropy]

end CapacityAtlas.FiniteDistribution
