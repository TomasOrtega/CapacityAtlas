/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Polynomial

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDerivAt_det_one_add_smul (M : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ ↦ det (1 + t • M)) (trace M) 0 := by
  have h := (det (1 + (X : ℝ[X]) • M.map C)).hasDerivAt 0
  rw [derivative_det_one_add_X_smul] at h
  have heval (t : ℝ) : (det (1 + (X : ℝ[X]) • M.map C)).eval t = det (1 + t • M) := by
    simp [eval_det, ← smul_eq_mul_diagonal]
  simpa only [heval] using h

theorem hasDerivAt_det_add_smul (A D : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ det (A + t • D)) (A.det * trace (A⁻¹ * D)) 0 := by
  have hfactor (t : ℝ) : A + t • D = A * (1 + t • (A⁻¹ * D)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hA)]
  simp_rw [hfactor, det_mul]
  exact (hasDerivAt_det_one_add_smul (A⁻¹ * D)).const_mul A.det

/-- The directional derivative of the real log determinant at an invertible matrix. -/
theorem hasDerivAt_log_det_add_smul (A D : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ Real.log (det (A + t • D))) (trace (A⁻¹ * D)) 0 := by
  have h := (hasDerivAt_det_add_smul A D hA).log (by simpa using hA)
  simpa only [zero_smul, add_zero, mul_div_cancel_left₀ _ hA] using h

theorem hasDerivAt_log_det_div_add_smul (A D B E : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ Real.log (det (A + t • D) / det (B + t • E)))
      (trace (A⁻¹ * D) - trace (B⁻¹ * E)) 0 := by
  have h := ((hasDerivAt_det_add_smul A D hA).div
    (hasDerivAt_det_add_smul B E hB) (by simpa using hB)).log
      (by simpa using div_ne_zero hA hB)
  simp only [Pi.div_apply, zero_smul, add_zero] at h
  convert! h using 1
  field_simp

end Matrix
