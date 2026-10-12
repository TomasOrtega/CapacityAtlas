/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Probability.GaussianBlocks
import Mathlib.RingTheory.Complex

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix

namespace CapacityAtlas.Gaussian.Interference

def complexMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.re, -z.im; z.im, z.re]

theorem complexMatrix_apply (z x : ℂ) :
    (complexMatrix z).toEuclideanLin (Complex.orthonormalBasisOneI.repr x) =
      Complex.orthonormalBasisOneI.repr (z * x) := by
  ext i
  fin_cases i <;> simp [complexMatrix, Matrix.toLpLin_apply,
    Complex.mul_re, Complex.mul_im] <;> ring

theorem complexMatrix_mul_transpose (z : ℂ) :
    complexMatrix z * (complexMatrix z).transpose = ‖z‖ ^ 2 • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.sq_norm,
      Complex.normSq_apply] <;> ring

variable {n : ℕ}

def complexBlockMatrix (z : Fin n → ℂ) :
    Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℝ :=
  blockDiagonal (fun t ↦ complexMatrix (z t))

noncomputable def realBlock (x : Fin n → ℂ) : EuclideanSpace ℝ (Fin 2 × Fin n) :=
  flattenGaussianBlock (fun t ↦ Complex.orthonormalBasisOneI.repr (x t))

noncomputable def complexBlock (x : EuclideanSpace ℝ (Fin 2 × Fin n)) : Fin n → ℂ :=
  fun t ↦ Complex.orthonormalBasisOneI.repr.symm (unflattenGaussianBlock x t)

@[simp] theorem complexBlock_realBlock (x : Fin n → ℂ) : complexBlock (realBlock x) = x := by
  ext t
  unfold complexBlock realBlock
  simp only [unflatten_flattenGaussianBlock, LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem realBlock_complexBlock (x : EuclideanSpace ℝ (Fin 2 × Fin n)) :
    realBlock (complexBlock x) = x := by
  unfold complexBlock realBlock
  simp only [LinearIsometryEquiv.apply_symm_apply, flatten_unflattenGaussianBlock]

@[fun_prop] theorem measurable_realBlock : Measurable (@realBlock n) := by
  unfold realBlock
  exact measurable_flattenGaussianBlock.comp
    (measurable_pi_lambda _ fun t ↦
      Complex.orthonormalBasisOneI.repr.continuous.measurable.comp (measurable_pi_apply t))

@[fun_prop] theorem measurable_complexBlock : Measurable (@complexBlock n) := by
  unfold complexBlock
  apply measurable_pi_lambda
  intro t
  exact Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.comp
    ((measurable_pi_apply t).comp measurable_unflattenGaussianBlock)

theorem realBlock_add (x y : Fin n → ℂ) : realBlock (x + y) = realBlock x + realBlock y := by
  ext ⟨i, t⟩
  simp [realBlock, flattenGaussianBlock]

theorem complexBlockMatrix_apply (z x : Fin n → ℂ) :
    (complexBlockMatrix z).toEuclideanLin (realBlock x) =
      realBlock (fun t ↦ z t * x t) := by
  ext ⟨i, t⟩
  change ((blockDiagonal (fun t ↦ complexMatrix (z t))) *ᵥ
    fun p ↦ Complex.orthonormalBasisOneI.repr (x p.2) p.1) (i, t) = _
  rw [blockDiagonal_mulVec_apply]
  exact congrArg (fun y : EuclideanSpace ℝ (Fin 2) ↦ y i) (complexMatrix_apply (z t) (x t))

theorem norm_realBlock_sq (x : Fin n → ℂ) : ‖realBlock x‖ ^ 2 = ∑ t, ‖x t‖ ^ 2 := by
  simp only [realBlock, EuclideanSpace.real_norm_sq_eq, flattenGaussianBlock,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [← EuclideanSpace.real_norm_sq_eq, LinearIsometryEquiv.norm_map]

theorem complexBlockMatrix_mul_transpose (z : Fin n → ℂ) :
    complexBlockMatrix z * (complexBlockMatrix z).transpose =
      blockDiagonal (fun t ↦ ‖z t‖ ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  simp only [complexBlockMatrix, blockDiagonal_transpose, ← blockDiagonal_mul,
    complexMatrix_mul_transpose]

theorem complexBlockMatrix_scalar_covariance (z : Fin n → ℂ) (e : ℝ) :
    complexBlockMatrix z * (e • 1) * (complexBlockMatrix z).transpose =
      blockDiagonal (fun t ↦ (e * ‖z t‖ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, complexBlockMatrix_mul_transpose,
    ← blockDiagonal_smul]
  congr 1
  funext t
  exact smul_smul e (‖z t‖ ^ 2) (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem complexBlockMatrix_residual_posSemidef (z : Fin n → ℂ) (e v : ℝ)
    (h : ∀ t, e * ‖z t‖ ^ 2 ≤ v) :
    (v • 1 - complexBlockMatrix z * (e • 1) * (complexBlockMatrix z).transpose).PosSemidef := by
  rw [complexBlockMatrix_scalar_covariance]
  have hv : v • (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℝ) =
      blockDiagonal (fun _ : Fin n ↦ v • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    change v • 1 = blockDiagonal (v • (1 : Fin n → Matrix (Fin 2) (Fin 2) ℝ))
    rw [blockDiagonal_smul, blockDiagonal_one]
  rw [hv, ← blockDiagonal_sub]
  apply posSemidef_blockDiagonal
  intro t
  simp only [Pi.sub_apply, ← sub_smul]
  exact PosSemidef.one.smul (sub_nonneg.mpr (h t))

end CapacityAtlas.Gaussian.Interference
