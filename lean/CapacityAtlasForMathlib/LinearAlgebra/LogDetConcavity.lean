/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianRelativeEntropy

open MeasureTheory ProbabilityTheory

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem PosDef.log_det_le_tangent {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    Real.log A.det ≤ Real.log B.det + trace (B⁻¹ * (A - B)) := by
  have h := ENNReal.toReal_nonneg (a :=
    InformationTheory.klDiv (multivariateGaussian (0 : EuclideanSpace ℝ ι) A)
      (multivariateGaussian 0 B))
  rw [CapacityAtlas.MeasureInformation.toReal_klDiv_multivariateGaussian 0 0 A B hA hB] at h
  simp only [sub_self, WithLp.ofLp_zero, mulVec_zero, dotProduct_zero, add_zero] at h
  rw [Matrix.mul_sub, trace_sub,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB.det_pos.ne'), trace_one]
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
lemma PosDef.convexCombination {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : (a • A + b • B).PosDef := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_add] at hab
    simpa only [zero_smul, zero_add, hab, one_smul] using hB
  · exact (hA.smul ha).add_posSemidef (hB.posSemidef.smul hb)

theorem log_det_concaveCombination {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * Real.log A.det + b * Real.log B.det ≤ Real.log (a • A + b • B).det := by
  let C := a • A + b • B
  have hC : C.PosDef := hA.convexCombination hB ha hb hab
  have h₁ := mul_le_mul_of_nonneg_left (hA.log_det_le_tangent hC) ha
  have h₂ := mul_le_mul_of_nonneg_left (hB.log_det_le_tangent hC) hb
  have hc : a • (A - C) + b • (B - C) = 0 := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
    exact sub_self C
  have ht : a * trace (C⁻¹ * (A - C)) + b * trace (C⁻¹ * (B - C)) = 0 := by
    have h := congrArg (fun Z ↦ trace (C⁻¹ * Z)) hc
    simpa only [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul,
      Matrix.mul_zero, trace_zero] using h
  have he : a * Real.log C.det + b * Real.log C.det = Real.log C.det := by
    rw [← add_mul, hab, one_mul]
  nlinarith

lemma PosDef.log_det_smul {A : Matrix ι ι ℝ} (hA : A.PosDef) {a : ℝ} (ha : 0 < a) :
    Real.log (a • A).det = (Fintype.card ι : ℝ) * Real.log a + Real.log A.det := by
  rw [det_smul, Real.log_mul (pow_ne_zero _ ha.ne') hA.det_pos.ne', Real.log_pow]

/-- Log-determinant concavity bounds a proportional stationary entropy difference. -/
theorem proportional_log_det_difference_le {A B X Y : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hX : X.PosDef) (hY : Y.PosDef)
    {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (hprop : a • B = A)
    (hshift : Y - X = B - A) :
    a * Real.log X.det - Real.log Y.det ≤ a * Real.log A.det - Real.log B.det := by
  have hcomb : a • Y = a • X + (1 - a) • A := by
    have hy : Y = X + (B - A) := by
      rw [eq_add_of_sub_eq hshift]
      abel
    rw [hy, smul_add, smul_sub, hprop, sub_smul, one_smul]
  have h := log_det_concaveCombination hX hA ha.le (sub_nonneg.mpr ha₁)
    (show a + (1 - a) = 1 by ring)
  rw [← hcomb, hY.log_det_smul ha] at h
  have hp := hB.log_det_smul ha
  rw [hprop] at hp
  nlinarith

theorem inv_proportional_smul {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a : ℝ} (h : B⁻¹ = a • A⁻¹) : a • B = A := by
  have hh := congrArg (fun Z ↦ A * Z * B) h
  simpa only [nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.mpr hB.det_pos.ne'),
    Matrix.mul_smul, Matrix.smul_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    Matrix.one_mul] using hh.symm

end Matrix
