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
      simpa only using
        (Fintype.prod_sum (fun i a => w a * h i a)).symm

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

/-- Distinct coordinates factor under a product mass. -/
@[capacity_shared_api]
theorem sum_mass_mul_apply_mul_apply (w f g : α → ℝ)
    (hw : ∑ a, w a = 1) {i j : ι} (hij : i ≠ j) :
    ∑ x : ι → α, mass w x * (f (x i) * g (x j)) =
      mean w f * mean w g := by
  let h : ι → α → ℝ := fun k a =>
    (if k = i then f a else 1) * (if k = j then g a else 1)
  calc
    ∑ x : ι → α, mass w x * (f (x i) * g (x j)) =
        ∑ x : ι → α, mass w x * ∏ k, h k (x k) := by
          apply Fintype.sum_congr
          intro x
          congr 1
          simp only [h, Finset.prod_mul_distrib]
          rw [Fintype.prod_eq_single i, Fintype.prod_eq_single j]
          · simp [hij, Ne.symm hij]
          · intro k hki
            simp [hki]
          · intro k hkj
            simp [hkj]
    _ = ∏ k, ∑ a, w a * h k a := sum_mass_mul_prod w h
    _ = mean w f * mean w g := by
      rw [Fintype.prod_eq_mul i j hij]
      · simp [h, mean, hij, Ne.symm hij]
      · intro k hk
        simp [h, hk.1, hk.2, hw]

/-- The second moment of a sum of centered coordinate observables is the sum of
its coordinate second moments. -/
@[capacity_shared_api]
theorem sum_mass_mul_centered_sum_sq (w : α → ℝ) (f : ι → α → ℝ)
    (hw : ∑ a, w a = 1) (hmean : ∀ i, mean w (f i) = 0) :
    ∑ x : ι → α, mass w x * (∑ i, f i (x i)) ^ 2 =
      ∑ i, mean w (fun a => (f i a) ^ 2) := by
  calc
    ∑ x : ι → α, mass w x * (∑ i, f i (x i)) ^ 2 =
        ∑ x : ι → α, ∑ i, ∑ j, mass w x * (f i (x i) * f j (x j)) := by
          apply Fintype.sum_congr
          intro x
          simp only [pow_two, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ x : ι → α, mass w x * (f i (x i) * f j (x j)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro i
      rw [Finset.sum_comm]
    _ = ∑ i, mean w (fun a => (f i a) ^ 2) := by
      apply Fintype.sum_congr
      intro i
      rw [Fintype.sum_eq_single i]
      · simpa only [pow_two] using
          sum_mass_mul_apply w (fun a => f i a * f i a) hw i
      · intro j hji
        rw [sum_mass_mul_apply_mul_apply w (f i) (f j) hw (Ne.symm hji)]
        simp [hmean]

end FiniteProductProbability

end CapacityAtlas
