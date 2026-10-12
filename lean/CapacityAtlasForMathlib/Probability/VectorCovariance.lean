/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.LinearAlgebra.Matrix.Trace

open MeasureTheory Matrix
open scoped BigOperators

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]

lemma covarianceQuadratic_eq_sum (m : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    (x - m) ⬝ᵥ A *ᵥ (x - m) = ∑ i, ∑ j, A i j * ((x i - m i) * (x j - m j)) := by
  simp only [dotProduct, mulVec, WithLp.ofLp_sub, Pi.sub_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma integrable_covarianceQuadratic
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ A *ᵥ (x - m)) μ := by
  simp_rw [covarianceQuadratic_eq_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (((hL2 i).sub (memLp_const (m i))).integrable_mul
    ((hL2 j).sub (memLp_const (m j)))).const_mul _

lemma integral_covarianceQuadratic_eq_sum
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ)
    (hm : ∀ i, (∫ x : EuclideanSpace ℝ ι, x i ∂μ) = m i) :
    (∫ x : EuclideanSpace ℝ ι, (x - m) ⬝ᵥ A *ᵥ (x - m) ∂μ) =
      ∑ i, ∑ j, A i j * covariance (fun x ↦ x i) (fun x ↦ x j) μ := by
  have hi (i j : ι) : Integrable
      (fun x : EuclideanSpace ℝ ι ↦ A i j * ((x i - m i) * (x j - m j))) μ :=
    (((hL2 i).sub (memLp_const (m i))).integrable_mul
      ((hL2 j).sub (memLp_const (m j)))).const_mul _
  simp_rw [covarianceQuadratic_eq_sum]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, covariance, hm i, hm j]

lemma integral_covarianceQuadratic_eq_trace
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m : EuclideanSpace ℝ ι) (A S : Matrix ι ι ℝ)
    (hm : ∀ i, (∫ x : EuclideanSpace ℝ ι, x i ∂μ) = m i)
    (hcov : ∀ i j, covariance (fun x : EuclideanSpace ℝ ι ↦ x i) (fun x ↦ x j) μ = S i j)
    (hS : S.IsSymm) :
    (∫ x : EuclideanSpace ℝ ι, (x - m) ⬝ᵥ A *ᵥ (x - m) ∂μ) = trace (A * S) := by
  rw [integral_covarianceQuadratic_eq_sum hL2 m A hm]
  simp_rw [hcov]
  unfold trace diag
  simp only [mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hS.apply i j]

lemma integral_inv_covarianceQuadratic [DecidableEq ι]
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hm : ∀ i, (∫ x : EuclideanSpace ℝ ι, x i ∂μ) = m i)
    (hcov : ∀ i j, covariance (fun x : EuclideanSpace ℝ ι ↦ x i) (fun x ↦ x j) μ = S i j) :
    (∫ x : EuclideanSpace ℝ ι, (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m) ∂μ) = Fintype.card ι := by
  have hsymm : S.IsSymm := isHermitian_iff_isSymm.mp hS.isHermitian
  rw [integral_covarianceQuadratic_eq_trace hL2 m S⁻¹ S hm hcov hsymm,
    S.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hS.det_pos.ne'), trace_one]

omit [Fintype ι] in
lemma integral_centered_coordinate_mul
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m a : EuclideanSpace ℝ ι) (hm : ∀ i, (∫ x : EuclideanSpace ℝ ι, x i ∂μ) = m i)
    (i j : ι) :
    (∫ x : EuclideanSpace ℝ ι, (x i - a i) * (x j - a j) ∂μ) =
      covariance (fun x ↦ x i) (fun x ↦ x j) μ + (m i - a i) * (m j - a j) := by
  rw [covariance_eq_sub (hL2 i) (hL2 j), hm i, hm j]
  simp_rw [sub_mul, mul_sub]
  rw [integral_sub, integral_sub, integral_sub, integral_mul_const, integral_const_mul,
    hm i, hm j]
  · simp only [integral_const, probReal_univ, one_smul, Pi.mul_apply]
    ring
  · exact (hL2 j).integrable (by simp) |>.const_mul _
  · exact integrable_const _
  · exact (hL2 i).integrable_mul (hL2 j)
  · exact (hL2 i).integrable (by simp) |>.mul_const _
  · exact ((hL2 i).integrable_mul (hL2 j)).sub
      ((hL2 i).integrable (by simp) |>.mul_const _)
  · exact ((hL2 j).integrable (by simp) |>.const_mul _).sub (integrable_const _)

lemma integral_quadratic_eq_trace_add
    (hL2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ)
    (m a : EuclideanSpace ℝ ι) (A S : Matrix ι ι ℝ)
    (hm : ∀ i, (∫ x : EuclideanSpace ℝ ι, x i ∂μ) = m i)
    (hcov : ∀ i j, covariance (fun x : EuclideanSpace ℝ ι ↦ x i) (fun x ↦ x j) μ = S i j)
    (hS : S.IsSymm) :
    (∫ x : EuclideanSpace ℝ ι, (x - a) ⬝ᵥ A *ᵥ (x - a) ∂μ) =
      trace (A * S) + (m - a) ⬝ᵥ A *ᵥ (m - a) := by
  have hi (i j : ι) : Integrable
      (fun x : EuclideanSpace ℝ ι ↦ A i j * ((x i - a i) * (x j - a j))) μ :=
    (((hL2 i).sub (memLp_const (a i))).integrable_mul
      ((hL2 j).sub (memLp_const (a j)))).const_mul _
  simp_rw [covarianceQuadratic_eq_sum]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j), integral_const_mul,
    integral_centered_coordinate_mul hL2 m a hm, hcov, mul_add,
    Finset.sum_add_distrib]
  congr 1
  unfold trace diag
  simp only [mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hS.apply i j]

end ProbabilityTheory
