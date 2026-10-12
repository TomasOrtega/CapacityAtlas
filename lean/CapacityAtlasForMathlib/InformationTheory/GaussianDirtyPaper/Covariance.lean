/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Matrix Real

namespace CapacityAtlas.Gaussian.DirtyPaper

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

def outputCovariance (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    Matrix ο ο ℝ := N + H * Q * H.transpose

noncomputable def costaCoefficient (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) : Matrix ι ο ℝ := Q * H.transpose * (outputCovariance H Q N)⁻¹

noncomputable def residualCovariance (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) : Matrix ι ι ℝ := Q - costaCoefficient H Q N * H * Q

omit [DecidableEq ι] [DecidableEq ο] in
theorem outputCovariance_posDef (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    (outputCovariance H Q N).PosDef := by
  apply hN.add_posSemidef
  simpa using hQ.mul_mul_conjTranspose_same H

theorem residualCovariance_eq_inverse (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hN : N.PosDef) :
    residualCovariance H Q N = (Q⁻¹ + H.transpose * N⁻¹ * H)⁻¹ := by
  have hC := outputCovariance_posDef H Q N hQ.posSemidef hN
  have hQi := Q.nonsing_inv_nonsing_inv (isUnit_iff_ne_zero.mpr hQ.det_pos.ne')
  have hNi := N.nonsing_inv_nonsing_inv (isUnit_iff_ne_zero.mpr hN.det_pos.ne')
  symm
  simpa only [hQi, hNi, residualCovariance, costaCoefficient,
    outputCovariance, Matrix.mul_assoc] using
    Q⁻¹.add_mul_mul_inv_eq_sub H.transpose N⁻¹ H hQ.inv.isUnit hN.inv.isUnit
      (by simpa only [hQi, hNi, outputCovariance] using hC.isUnit)

theorem residualCovariance_posDef (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hN : N.PosDef) :
    (residualCovariance H Q N).PosDef := by
  rw [residualCovariance_eq_inverse H Q N hQ hN]
  apply Matrix.PosDef.inv
  apply hQ.inv.add_posSemidef
  simpa using hN.inv.posSemidef.conjTranspose_mul_mul_same H

omit [DecidableEq ι] in
theorem costaCoefficient_mul_outputCovariance (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    costaCoefficient H Q N * outputCovariance H Q N = Q * H.transpose := by
  rw [costaCoefficient, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (outputCovariance_posDef H Q N hQ hN).det_pos.ne'), Matrix.mul_one]

theorem det_residualCovariance (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    (residualCovariance H Q N).det = Q.det * N.det / (outputCovariance H Q N).det := by
  have hC := outputCovariance_posDef H Q N hQ hN
  have hfactor : residualCovariance H Q N =
      Q * (1 - (H.transpose * (outputCovariance H Q N)⁻¹) * (H * Q)) := by
    simp only [residualCovariance, costaCoefficient, mul_sub, mul_one, Matrix.mul_assoc]
  have hcancel : 1 - (H * Q) * (H.transpose * (outputCovariance H Q N)⁻¹) =
      N * (outputCovariance H Q N)⁻¹ := by
    have hc := (outputCovariance H Q N).mul_nonsing_inv
      (isUnit_iff_ne_zero.mpr hC.det_pos.ne')
    rw [outputCovariance, add_mul] at hc
    rw [← hc]
    simp only [outputCovariance, Matrix.mul_assoc]
    abel
  rw [hfactor, det_mul, det_one_sub_mul_comm, hcancel, det_mul, det_nonsing_inv,
    Ring.inverse_eq_inv]
  ring

theorem log_det_residualCovariance (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hN : N.PosDef) :
    log Q.det - log (residualCovariance H Q N).det =
      log (outputCovariance H Q N).det - log N.det := by
  rw [det_residualCovariance H Q N hQ.posSemidef hN,
    log_div (mul_pos hQ.det_pos hN.det_pos).ne'
      (outputCovariance_posDef H Q N hQ.posSemidef hN).det_pos.ne',
    log_mul hQ.det_pos.ne' hN.det_pos.ne']
  ring

theorem residualCrossCovariance_zero (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    (1 - costaCoefficient H Q N * H) * Q * H.transpose - costaCoefficient H Q N * N = 0 := by
  have h := costaCoefficient_mul_outputCovariance H Q N hQ hN
  rw [outputCovariance, Matrix.mul_add] at h
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc] at h ⊢
  calc
    _ = Q * H.transpose - (costaCoefficient H Q N * N +
        costaCoefficient H Q N * (H * (Q * H.transpose))) := by abel
    _ = 0 := by rw [h, sub_self]

theorem residualCovariance_eq_independent (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hN : N.PosDef) :
    residualCovariance H Q N =
      (1 - costaCoefficient H Q N * H) * Q * (1 - costaCoefficient H Q N * H).transpose +
        costaCoefficient H Q N * N * (costaCoefficient H Q N).transpose := by
  have hcross : (1 - costaCoefficient H Q N * H) * Q * H.transpose =
      costaCoefficient H Q N * N := by
    exact sub_eq_zero.mp (residualCrossCovariance_zero H Q N hQ hN)
  rw [transpose_sub, transpose_one, transpose_mul, mul_sub, mul_one,
    ← Matrix.mul_assoc, hcross]
  simp only [sub_add_cancel, sub_mul, one_mul, residualCovariance]

end CapacityAtlas.Gaussian.DirtyPaper
