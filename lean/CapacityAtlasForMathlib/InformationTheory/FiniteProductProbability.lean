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

omit [Fintype α] [DecidableEq ι] in
@[capacity_shared_api]
theorem mass_nonnegative (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (x : ι → α) :
    0 ≤ mass w x :=
  Finset.prod_nonneg fun i _ ↦ hw (x i)

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

/-- A coordinate of a product with coordinate-dependent masses has its prescribed mean. -/
@[capacity_shared_api]
theorem sum_prod_mul_apply (w : ι → α → ℝ) (f : α → ℝ)
    (hw : ∀ i, ∑ a, w i a = 1) (i : ι) :
    ∑ x : ι → α, (∏ j, w j (x j)) * f (x i) =
      ∑ a, w i a * f a := by
  let h : ι → α → ℝ := fun j a ↦ if j = i then f a else 1
  calc
    ∑ x : ι → α, (∏ j, w j (x j)) * f (x i) =
        ∑ x : ι → α, ∏ j, (w j (x j) * h j (x j)) := by
      apply Fintype.sum_congr
      intro x
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Fintype.prod_eq_single i]
      · simp [h]
      · intro j hji
        simp [h, hji]
    _ = ∏ j, ∑ a, w j a * h j a := by
      simpa only using
        (Fintype.prod_sum (fun j a ↦ w j a * h j a)).symm
    _ = ∑ a, w i a * f a := by
      rw [Fintype.prod_eq_single i]
      · simp [h]
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
  let h : ι → α → ℝ := fun k a ↦
    (if k = i then f a else 1) * (if k = j then g a else 1)
  calc
    ∑ x : ι → α, mass w x * (f (x i) * g (x j)) =
        ∑ x : ι → α, mass w x * ∏ k, h k (x k) := by
          apply Fintype.sum_congr
          intro x
          congr 1
          simp only [h, Finset.prod_mul_distrib]
          rw [Fintype.prod_eq_single i, Fintype.prod_eq_single j]
          · simp
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
      ∑ i, mean w (fun a ↦ (f i a) ^ 2) := by
  calc
    ∑ x : ι → α, mass w x * (∑ i, f i (x i)) ^ 2 =
        ∑ x : ι → α, ∑ i, ∑ j, mass w x * (f i (x i) * f j (x j)) := by
          apply Fintype.sum_congr
          intro x
          simp only [pow_two, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ x : ι → α, mass w x * (f i (x i) * f j (x j)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro i
      rw [Finset.sum_comm]
    _ = ∑ i, mean w (fun a ↦ (f i a) ^ 2) := by
      apply Fintype.sum_congr
      intro i
      rw [Fintype.sum_eq_single i]
      · simpa only [pow_two] using
          sum_mass_mul_apply w (fun a ↦ f i a * f i a) hw i
      · intro j hji
        rw [sum_mass_mul_apply_mul_apply w (f i) (f j) hw (Ne.symm hji)]
        simp [hmean]

/-- Some value is at most its average under nonnegative normalized weights. -/
@[capacity_shared_api]
theorem exists_value_le_weighted_mean [Nonempty α] (w f : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) :
    ∃ a, f a ≤ ∑ b, w b * f b := by
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨a, ?_⟩
  calc
    f a = ∑ b, w b * f a := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ b, w b * f b := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (ha b hb) (hw b)

/-- A finite weighted form of the lower-tail Chebyshev inequality. -/
@[capacity_shared_api]
theorem lowerTail_mass_le_secondMoment_div_sq (w f : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (center δ : ℝ) (hδ : 0 < δ) :
    (∑ a, if f a ≤ center - δ then w a else 0) ≤
      (∑ a, w a * (f a - center) ^ 2) / δ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · have hsquare : δ ^ 2 ≤ (f a - center) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsquare (hw a)
  · simpa only [zero_mul] using mul_nonneg (hw a) (sq_nonneg (f a - center))

end FiniteProductProbability

end CapacityAtlas
