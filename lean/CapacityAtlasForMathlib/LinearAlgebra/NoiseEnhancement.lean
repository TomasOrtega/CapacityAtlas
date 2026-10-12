/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.LinearAlgebra.PositiveTrace

open scoped MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma PosDef.inv_antitone {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have h₁ := (le_iff.mp hAB).conjTranspose_mul_mul_same B⁻¹
  have h₂ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  rw [hB.inv.isHermitian.eq] at h₁
  rw [(hA.inv.isHermitian.sub hB.inv.isHermitian).eq] at h₂
  have ha : A * A⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hai : A⁻¹ * A = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hb : B⁻¹ * B = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  have he : B⁻¹ * (B - A) * B⁻¹ + (A⁻¹ - B⁻¹) * A * (A⁻¹ - B⁻¹) = A⁻¹ - B⁻¹ := by
    calc
      _ = B⁻¹ * B * B⁻¹ + A⁻¹ * A * A⁻¹ - A⁻¹ * A * B⁻¹ - B⁻¹ * (A * A⁻¹) := by
        noncomm_ring
      _ = _ := by rw [ha, hai, hb]; simp
  exact le_iff.mpr (he ▸ h₁.add h₂)

noncomputable def enhancedNoise (X M : Matrix ι ι ℝ) : Matrix ι ι ℝ := (X⁻¹ + M)⁻¹

lemma enhancedNoise_posDef {X M : Matrix ι ι ℝ} (hX : X.PosDef) (hM : M.PosSemidef) :
    (enhancedNoise X M).PosDef := (hX.inv.add_posSemidef hM).inv

lemma enhancedNoise_le {X M : Matrix ι ι ℝ} (hX : X.PosDef) (hM : M.PosSemidef) :
    enhancedNoise X M ≤ X := by
  have h := hX.inv.inv_antitone (hX.inv.add_posSemidef hM)
    (le_add_of_nonneg_right hM.nonneg)
  simpa only [enhancedNoise, nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hX.det_pos.ne')]
    using h

lemma enhancedNoise_inv {X M : Matrix ι ι ℝ} (hX : X.PosDef) (hM : M.PosSemidef) :
    (enhancedNoise X M)⁻¹ = X⁻¹ + M :=
  nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hX.inv.add_posSemidef hM).det_pos.ne')

lemma enhancedNoise_add_mul {X M : Matrix ι ι ℝ} (hX : X.PosDef) (hM : M.PosSemidef) :
    enhancedNoise X M + X * M * enhancedNoise X M = X := by
  have h := mul_nonsing_inv (X⁻¹ + M)
    (isUnit_iff_ne_zero.mpr (hX.inv.add_posSemidef hM).det_pos.ne')
  have hh := congrArg (X * ·) h
  simpa only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc,
    mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hX.det_pos.ne'), Matrix.one_mul,
    Matrix.mul_one, enhancedNoise] using hh

/-- A precision increment orthogonal to the signal preserves the signal-plus-noise inverse. -/
theorem inv_add_enhancedNoise {B X M : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (hX : X.PosDef) (hM : M.PosSemidef) (hBM : B * M = 0) :
    (B + enhancedNoise X M)⁻¹ = (B + X)⁻¹ + M := by
  have hMB : M * B = 0 := by
    have h := congrArg conjTranspose hBM
    simpa only [conjTranspose_mul, hB.isHermitian.eq, hM.isHermitian.eq, conjTranspose_zero] using h
  have hBX : (B + X).PosDef := by simpa only [add_comm] using hX.add_posSemidef hB
  have hunit : IsUnit (B + X).det := isUnit_iff_ne_zero.mpr hBX.det_pos.ne'
  apply inv_eq_left_inv
  have h : (B + X) * ((B + X)⁻¹ + M) * (B + enhancedNoise X M) = (B + X) * 1 := by
    rw [Matrix.mul_add (B + X) (B + X)⁻¹ M, mul_nonsing_inv _ hunit]
    simp only [Matrix.add_mul, hBM, zero_add, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.mul_assoc X M B, hMB, Matrix.mul_zero, zero_add]
    rw [add_assoc B, enhancedNoise_add_mul hX hM]
  have hh := congrArg (fun A ↦ (B + X)⁻¹ * A) h
  simpa only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hunit] using hh

lemma det_add_div_det_eq_det_one_add {B X : Matrix ι ι ℝ} (hX : X.PosDef) :
    (B + X).det / X.det = (1 + B * X⁻¹).det := by
  have h : (B + X) * X⁻¹ = 1 + B * X⁻¹ := by
    rw [Matrix.add_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hX.det_pos.ne')]
    exact add_comm _ _
  rw [← h, det_mul, det_nonsing_inv, Ring.inverse_eq_inv, div_eq_mul_inv]

theorem detRatio_enhancedNoise {B X M : Matrix ι ι ℝ}
    (hX : X.PosDef) (hM : M.PosSemidef) (hBM : B * M = 0) :
    (B + enhancedNoise X M).det / (enhancedNoise X M).det = (B + X).det / X.det := by
  rw [det_add_div_det_eq_det_one_add (enhancedNoise_posDef hX hM),
    det_add_div_det_eq_det_one_add hX, enhancedNoise_inv hX hM, Matrix.mul_add, hBM, add_zero]

theorem weighted_inv_add_enhancedNoise {B X O : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (hX : X.PosDef) (hO : O.PosSemidef) (hBO : B * O = 0) {a : ℝ} (ha : 0 < a) :
    a • (B + enhancedNoise X (a⁻¹ • O))⁻¹ = a • (B + X)⁻¹ + O := by
  rw [inv_add_enhancedNoise hB hX (hO.smul (inv_nonneg.mpr ha.le))
    (by rw [Matrix.mul_smul, hBO, smul_zero])]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

noncomputable def intermediateNoise (B X O : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  enhancedNoise (B + X) O - B

lemma add_intermediateNoise (B X O : Matrix ι ι ℝ) :
    B + intermediateNoise B X O = enhancedNoise (B + X) O := by
  unfold intermediateNoise
  rw [add_comm, sub_add_cancel]

/-- Proportional weighted precisions bound the enhanced noise between adjacent noises. -/
theorem intermediateNoise_bounds {B X₁ X₂ O : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (hX₁ : X₁.PosDef) (hX₂ : X₂.PosDef) (hO : O.PosSemidef)
    {a : ℝ} (ha : a ≤ 1)
    (hprop : (B + X₂)⁻¹ + O = a • (B + X₁)⁻¹) :
    X₁ ≤ intermediateNoise B X₂ O ∧ intermediateNoise B X₂ O ≤ X₂ := by
  have h₁ : (B + X₁).PosDef := by simpa only [add_comm] using hX₁.add_posSemidef hB
  have h₂ : (B + X₂).PosDef := by simpa only [add_comm] using hX₂.add_posSemidef hB
  have hp : ((B + X₂)⁻¹ + O).PosDef := h₂.inv.add_posSemidef hO
  have hle : (B + X₂)⁻¹ + O ≤ (B + X₁)⁻¹ := by
    rw [hprop, le_iff]
    simpa only [sub_smul, one_smul] using
      h₁.inv.posSemidef.smul (sub_nonneg.mpr ha)
  have hlow := hp.inv_antitone h₁.inv hle
  rw [nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr h₁.det_pos.ne')] at hlow
  refine ⟨?_, ?_⟩
  · simpa only [intermediateNoise, enhancedNoise, add_sub_cancel_left] using
      sub_le_sub_right hlow B
  · simpa only [intermediateNoise, add_sub_cancel_left] using
      sub_le_sub_right (enhancedNoise_le h₂ hO) B

theorem intermediateNoise_posDef {B X₁ X₂ O : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (hX₁ : X₁.PosDef) (hX₂ : X₂.PosDef) (hO : O.PosSemidef)
    {a : ℝ} (ha : a ≤ 1)
    (hprop : (B + X₂)⁻¹ + O = a • (B + X₁)⁻¹) :
    (intermediateNoise B X₂ O).PosDef := by
  have hlow := (intermediateNoise_bounds hB hX₁ hX₂ hO ha hprop).1
  convert hX₁.add_posSemidef (le_iff.mp hlow) using 1
  rw [add_comm, sub_add_cancel]

theorem inv_add_intermediateNoise {B X O : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (hX : X.PosDef) (hO : O.PosSemidef) :
    (B + intermediateNoise B X O)⁻¹ = (B + X)⁻¹ + O := by
  rw [add_intermediateNoise]
  exact enhancedNoise_inv (by simpa only [add_comm] using hX.add_posSemidef hB) hO

theorem detRatio_intermediateNoise {B C X O : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (hX : X.PosDef) (hO : O.PosSemidef) (hCO : C * O = 0) :
    (C + (B + intermediateNoise B X O)).det / (B + intermediateNoise B X O).det =
      (C + (B + X)).det / (B + X).det := by
  rw [add_intermediateNoise]
  exact detRatio_enhancedNoise (by simpa only [add_comm] using hX.add_posSemidef hB) hO hCO

end Matrix
