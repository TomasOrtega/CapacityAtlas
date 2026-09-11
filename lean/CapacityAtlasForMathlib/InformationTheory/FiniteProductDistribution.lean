/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteEntropy
import CapacityAtlasForMathlib.InformationTheory.DecoderSideInformation

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]

/-- Independent coordinates with a prescribed distribution at each index. -/
@[capacity_shared_api]
def productFamily (distributions : I → FiniteDistribution A) :
    FiniteDistribution (I → A) where
  probability word := ∏ i, distributions i (word i)
  nonnegative word := Finset.prod_nonneg fun i _ ↦ (distributions i).nonnegative (word i)
  sum_probability := by
    rw [← Fintype.prod_sum]
    simp

@[simp, capacity_shared_api]
theorem productFamily_apply (distributions : I → FiniteDistribution A) (word : I → A) :
    productFamily distributions word = ∏ i, distributions i (word i) := rfl

/-- An observable of one coordinate has the prescribed marginal expectation. -/
@[capacity_shared_api]
theorem sum_productFamily_mul_eval (distributions : I → FiniteDistribution A)
    (observable : A → ℝ) (i : I) :
    ∑ word, productFamily distributions word * observable (word i) =
      ∑ a, distributions i a * observable a :=
  FiniteProductProbability.sum_prod_mul_apply (fun j a ↦ distributions j a) observable
    (fun j ↦ (distributions j).sum_probability) i

@[simp, capacity_shared_api]
theorem map_productFamily_eval [DecidableEq A] (distributions : I → FiniteDistribution A)
    (i : I) : (productFamily distributions).map (fun word ↦ word i) = distributions i := by
  ext a
  change (∑ word with word i = a, productFamily distributions word) = distributions i a
  simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using
    sum_productFamily_mul_eval distributions (fun x ↦ if x = a then 1 else 0) i

omit [Fintype I] [DecidableEq I] in
@[simp, capacity_shared_api]
theorem productFamily_const_eq_iid (distribution : FiniteDistribution A) (n : ℕ) :
    productFamily (fun _ : Fin n ↦ distribution) = distribution.iid n := by
  ext word
  rfl

section Independent

variable {B C D : Type*} [Fintype B] [Fintype C] [Fintype D]

omit [Fintype I] [DecidableEq I] in
/-- Separate deterministic observations preserve independence. -/
@[capacity_shared_api]
theorem map_joint_independent [DecidableEq C] [DecidableEq D]
    (first : FiniteDistribution A) (second : FiniteDistribution B)
    (f : A → C) (g : B → D) :
    (first.joint (fun _ ↦ second)).map (fun pair ↦ (f pair.1, g pair.2)) =
      (first.map f).joint (fun _ ↦ second.map g) := by
  classical
  ext pair
  rcases pair with ⟨c, d⟩
  change (∑ pair : A × B with (f pair.1, g pair.2) = (c, d), first pair.1 * second pair.2) =
    (∑ a with f a = c, first a) * ∑ b with g b = d, second b
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all

/-- Evaluation of independent product families gives independent coordinate marginals. -/
@[capacity_shared_api]
theorem map_joint_productFamily_eval {J : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq A] [DecidableEq B]
    (first : I → FiniteDistribution A) (second : J → FiniteDistribution B) (i : I) (j : J) :
    ((productFamily first).joint (fun _ ↦ productFamily second)).map
        (fun pair ↦ (pair.1 i, pair.2 j)) =
      (first i).joint (fun _ ↦ second j) := by
  rw [map_joint_independent (productFamily first) (productFamily second)
    (fun word ↦ word i) (fun word ↦ word j), map_productFamily_eval, map_productFamily_eval]

end Independent

end CapacityAtlas.FiniteDistribution
