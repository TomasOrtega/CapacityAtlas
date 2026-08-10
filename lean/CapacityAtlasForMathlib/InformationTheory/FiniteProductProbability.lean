/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasUtil.Metadata
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteProductProbability

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

/-- Unnormalized product mass associated with a one-coordinate mass function. -/
@[capacity_shared_api]
def mass (w : α → ℝ) (x : ι → α) : ℝ :=
  ∏ i, w (x i)

/-- Expectation of a one-coordinate observable. -/
@[capacity_shared_api]
def mean (w f : α → ℝ) : ℝ :=
  ∑ a, w a * f a

/-- Product masses are normalized when the coordinate masses are normalized. -/
@[capacity_shared_api]
theorem sum_mass (w : α → ℝ) (hw : ∑ a, w a = 1) :
    ∑ x : ι → α, mass w x = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp [hw]

/-- Expectation of a product of coordinate observables under a product mass. -/
@[capacity_shared_api]
theorem sum_mass_mul_prod (w : α → ℝ) (h : ι → α → ℝ) :
    ∑ x : ι → α, mass w x * ∏ i, h i (x i) =
      ∏ i, ∑ a, w a * h i a := by
  calc
    ∑ x : ι → α, mass w x * ∏ i, h i (x i) =
        ∑ x : ι → α, ∏ i, (w (x i) * h i (x i)) := by
          apply Fintype.sum_congr
          intro x
          simp only [mass, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a, w a * h i a := by
      rw [← Fintype.prod_sum]

/-- A coordinate has its prescribed one-coordinate expectation. -/
@[capacity_shared_api]
theorem sum_mass_mul_apply (w f : α → ℝ) (hw : ∑ a, w a = 1) (i : ι) :
    ∑ x : ι → α, mass w x * f (x i) = mean w f := by
  let h : ι → α → ℝ := fun j a => if j = i then f a else 1
  calc
    ∑ x : ι → α, mass w x * f (x i) =
        ∑ x : ι → α, mass w x * ∏ j, h j (x j) := by
          apply Fintype.sum_congr
          intro x
          congr 1
          rw [Fintype.prod_eq_single i]
          · simp [h]
          · intro j hji
            simp [h, hji]
    _ = ∏ j, ∑ a, w a * h j a := sum_mass_mul_prod w h
    _ = mean w f := by
      rw [Fintype.prod_eq_single i]
      · simp [h, mean]
      · intro j hji
        simp [h, hji, hw]

/-- Expectation commutes with a finite sum of coordinate observables. -/
@[capacity_shared_api]
theorem sum_mass_mul_sum (w : α → ℝ) (f : ι → α → ℝ)
    (hw : ∑ a, w a = 1) :
    ∑ x : ι → α, mass w x * ∑ i, f i (x i) =
      ∑ i, mean w (f i) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i
  exact sum_mass_mul_apply w (f i) hw i

end FiniteProductProbability

end CapacityAtlas
