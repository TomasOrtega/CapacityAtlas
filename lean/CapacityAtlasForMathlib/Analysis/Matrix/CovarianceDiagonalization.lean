/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.Matrix.Order

open scoped MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Simultaneous congruence reduces a positive covariance direction to the identity. -/
theorem exists_diagonalization_covariance_affine
    (N D : Matrix ι ι ℝ) (hN : N.PosSemidef) (hD : D.PosDef) :
    ∃ (A : Matrix ι ι ℝ) (c : ι → ℝ),
      A.det ≠ 0 ∧ (∀ i, 0 ≤ c i) ∧
      (∀ t : ℝ, N + t • D = A * diagonal (fun i ↦ c i + t) * A.transpose) := by
  let R := CFC.sqrt D
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)
  have hRdet : R.det ≠ 0 := by
    dsimp [R]
    rw [hD.posSemidef.det_sqrt, RCLike.sqrt_of_nonneg hD.det_pos.le]
    exact (Real.sqrt_pos.mpr hD.det_pos).ne'
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hRdet)
  have hiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hRdet)
  have hRt : R.transpose = R := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hRit : R⁻¹.transpose = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRt]
  let W := R⁻¹ * N * R⁻¹
  have hW : W.PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hRit] using hN.mul_mul_conjTranspose_same R⁻¹
  let U : Matrix ι ι ℝ := hW.isHermitian.eigenvectorUnitary
  have hU : U * U.transpose = 1 := by
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hW.isHermitian.eigenvectorUnitary
  have hUdet : U.det ≠ 0 :=
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det U).mp Unitary.isUnit_coe))
  let c := hW.isHermitian.eigenvalues
  have hs : W = U * diagonal c * U.transpose := by
    simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq] using hW.isHermitian.spectral_theorem
  have hNform : N = (R * U) * diagonal c * (R * U).transpose := by
    calc
      N = R * W * R := by
        dsimp [W]
        calc
          N = (R * R⁻¹) * N * (R⁻¹ * R) := by rw [hRi, hiR, one_mul, mul_one]
          _ = _ := by noncomm_ring
      _ = _ := by rw [hs, Matrix.transpose_mul, hRt]; noncomm_ring
  have hDform : D = (R * U) * (R * U).transpose := by
    rw [Matrix.transpose_mul, hRt, mul_assoc, ← mul_assoc U U.transpose, hU, one_mul]
    exact (CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg).symm
  refine ⟨R * U, c, ?_, hW.eigenvalues_nonneg, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero hRdet hUdet
  · intro t
    rw [show diagonal (fun i ↦ c i + t) = diagonal c + t • (1 : Matrix ι ι ℝ) by
      rw [← diagonal_add, ← Matrix.diagonal_one, ← diagonal_smul]
      simp only [Pi.smul_def, smul_eq_mul, mul_one]]
    rw [Matrix.mul_add, Matrix.add_mul, hNform, hDform, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]

end Matrix
