/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Probability.GaussianChannel
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace

open MeasureTheory Matrix
open scoped ENNReal RealInnerProductSpace

namespace Matrix

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [DecidableEq ι] in
theorem blockDiagonal_mulVec_apply (N : τ → Matrix ι ι ℝ) (x : ι × τ → ℝ)
    (i : ι) (s : τ) : (blockDiagonal N *ᵥ x) (i, s) = (N s *ᵥ (fun j ↦ x (j, s))) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]

omit [DecidableEq ι] in
theorem dotProduct_blockDiagonal_mulVec (N : τ → Matrix ι ι ℝ) (x : ι × τ → ℝ) :
    x ⬝ᵥ blockDiagonal N *ᵥ x = ∑ s, (fun i ↦ x (i, s)) ⬝ᵥ N s *ᵥ (fun i ↦ x (i, s)) := by
  simp only [dotProduct, Fintype.sum_prod_type, blockDiagonal_mulVec_apply]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem posSemidef_blockDiagonal (N : τ → Matrix ι ι ℝ) (hN : ∀ s, (N s).PosSemidef) :
    (blockDiagonal N).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · change (blockDiagonal N).conjTranspose = _
    simp only [blockDiagonal_conjTranspose, (hN _).isHermitian.eq]
  · intro x
    simp only [star_trivial, dotProduct_blockDiagonal_mulVec]
    exact Finset.sum_nonneg (fun s _ ↦ by simpa using (hN s).dotProduct_mulVec_nonneg _)

omit [DecidableEq ι] in
theorem posDef_blockDiagonal (N : τ → Matrix ι ι ℝ) (hN : ∀ s, (N s).PosDef) :
    (blockDiagonal N).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(posSemidef_blockDiagonal N (fun s ↦ (hN s).posSemidef)).isHermitian, ?_⟩
  intro x hx
  obtain ⟨⟨i, s⟩, hxi⟩ := Function.ne_iff.mp hx
  have hs : (fun j ↦ x (j, s)) ≠ 0 := by
    intro he
    exact hxi (congrFun he i)
  simp only [star_trivial, dotProduct_blockDiagonal_mulVec]
  exact Finset.sum_pos' (fun t _ ↦ by simpa using (hN t).posSemidef.dotProduct_mulVec_nonneg _)
    ⟨s, Finset.mem_univ s, by simpa using (hN s).dotProduct_mulVec_pos hs⟩

theorem inv_blockDiagonal_posDef (N : τ → Matrix ι ι ℝ) (hN : ∀ s, (N s).PosDef) :
    (blockDiagonal N)⁻¹ = blockDiagonal (fun s ↦ (N s)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [← blockDiagonal_mul]
  simp only [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hN _).det_pos.ne')]
  exact blockDiagonal_one

theorem log_det_blockDiagonal_posDef (N : τ → Matrix ι ι ℝ) (hN : ∀ s, (N s).PosDef) :
    Real.log (blockDiagonal N).det = ∑ s, Real.log (N s).det := by
  rw [det_blockDiagonal, Real.log_prod (fun s _ ↦ (hN s).det_pos.ne')]

end Matrix

namespace ProbabilityTheory

variable {ι τ : Type*}

def flattenGaussianBlock (x : τ → EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι × τ) :=
  WithLp.toLp 2 (fun p ↦ x p.2 p.1)

def unflattenGaussianBlock (y : EuclideanSpace ℝ (ι × τ)) : τ → EuclideanSpace ℝ ι :=
  fun s ↦ WithLp.toLp 2 (fun i ↦ y (i, s))

@[simp] theorem flatten_unflattenGaussianBlock (y : EuclideanSpace ℝ (ι × τ)) :
    flattenGaussianBlock (unflattenGaussianBlock y) = y := by rfl

@[simp] theorem unflatten_flattenGaussianBlock (x : τ → EuclideanSpace ℝ ι) :
    unflattenGaussianBlock (flattenGaussianBlock x) = x := by rfl

@[fun_prop] theorem measurable_flattenGaussianBlock :
    Measurable (flattenGaussianBlock (ι := ι) (τ := τ)) := by
  unfold flattenGaussianBlock
  fun_prop

@[fun_prop] theorem measurable_unflattenGaussianBlock :
    Measurable (unflattenGaussianBlock (ι := ι) (τ := τ)) := by
  unfold unflattenGaussianBlock
  fun_prop

variable [Fintype ι] [Fintype τ]

theorem inner_flattenGaussianBlock (x : τ → EuclideanSpace ℝ ι)
    (t : EuclideanSpace ℝ (ι × τ)) :
    ⟪flattenGaussianBlock x, t⟫ =
      ⟪WithLp.toLp 2 x, WithLp.toLp 2 (unflattenGaussianBlock t)⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, flattenGaussianBlock,
    unflattenGaussianBlock, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem charFun_flattenGaussianBlock (μ : τ → Measure (EuclideanSpace ℝ ι))
    [∀ s, IsProbabilityMeasure (μ s)] (t : EuclideanSpace ℝ (ι × τ)) :
    charFun ((Measure.pi μ).map flattenGaussianBlock) t =
      ∏ s, charFun (μ s) (unflattenGaussianBlock t s) := by
  rw [← charFun_pi (μ := μ) (WithLp.toLp 2 (unflattenGaussianBlock t))]
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_flattenGaussianBlock]

variable [DecidableEq ι] [DecidableEq τ]

theorem map_flatten_pi_multivariateGaussian_zero (N : τ → Matrix ι ι ℝ)
    (hN : ∀ s, (N s).PosSemidef) :
    (Measure.pi (fun s ↦ multivariateGaussian 0 (N s))).map flattenGaussianBlock =
      multivariateGaussian 0 (blockDiagonal N) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_flattenGaussianBlock, charFun_multivariateGaussian (posSemidef_blockDiagonal N hN)]
  simp_rw [charFun_multivariateGaussian (hN _)]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  rw [dotProduct_blockDiagonal_mulVec]
  simp only [Complex.ofReal_sum, Finset.sum_div, Finset.sum_neg_distrib,
    unflattenGaussianBlock, WithLp.ofLp_toLp]

theorem map_flatten_pi_multivariateGaussian (m : τ → EuclideanSpace ℝ ι)
    (N : τ → Matrix ι ι ℝ) (hN : ∀ s, (N s).PosSemidef) :
    (Measure.pi (fun s ↦ multivariateGaussian (m s) (N s))).map flattenGaussianBlock =
      multivariateGaussian (flattenGaussianBlock m) (blockDiagonal N) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_flattenGaussianBlock, charFun_multivariateGaussian (posSemidef_blockDiagonal N hN)]
  simp_rw [charFun_multivariateGaussian (hN _)]
  rw [← Complex.exp_sum, real_inner_comm (flattenGaussianBlock m) t, inner_flattenGaussianBlock,
    real_inner_comm (WithLp.toLp 2 (unflattenGaussianBlock t)) (WithLp.toLp 2 m)]
  congr 1
  rw [dotProduct_blockDiagonal_mulVec]
  simp only [PiLp.inner_apply, Complex.ofReal_sum, Finset.sum_mul,
    Finset.sum_div, Finset.sum_sub_distrib, unflattenGaussianBlock,
    WithLp.ofLp_toLp]

end ProbabilityTheory
