/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianFisherTrace
import CapacityAtlasForMathlib.InformationTheory.GaussianAffineDeBruijn
import CapacityAtlasForMathlib.InformationTheory.EntropyPowerCalculus
import CapacityAtlasForMathlib.InformationTheory.GaussianEntropyAsymptotics

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal MatrixOrder

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Entropy power in nats, normalized so covariance `tI` has power `t`. -/
noncomputable def entropyPower (μ : Measure (EuclideanSpace ℝ ι)) : ℝ :=
  exp (2 * entropyWith μ volume / (Fintype.card ι : ℝ) - (log (2 * π) + 1))

omit [DecidableEq ι] in
lemma entropyPower_pos (μ : Measure (EuclideanSpace ℝ ι)) : 0 < entropyPower μ :=
  exp_pos _

lemma entropyPower_multivariateGaussian [Nonempty ι]
    (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    entropyPower (multivariateGaussian m N) = exp (log N.det / (Fintype.card ι : ℝ)) := by
  rw [entropyPower, entropyWith_multivariateGaussian m N hN]
  congr 1
  have hd : (Fintype.card ι : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  field_simp
  ring

lemma entropyPower_multivariateGaussian_isotropic [Nonempty ι]
    (m : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    entropyPower (multivariateGaussian m (t • (1 : Matrix ι ι ℝ))) = t := by
  rw [entropyPower_multivariateGaussian m _ (Matrix.PosDef.one.smul ht), Matrix.det_smul,
    Matrix.det_one, mul_one, log_pow]
  have hd : (Fintype.card ι : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  rw [mul_div_cancel_left₀ _ hd, exp_log ht]

lemma entropyPower_multivariateGaussian_smul [Nonempty ι]
    (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    {t : ℝ} (ht : 0 < t) :
    entropyPower (multivariateGaussian m (t • N)) =
      t * entropyPower (multivariateGaussian m N) := by
  rw [entropyPower_multivariateGaussian m _ (hN.smul ht),
    entropyPower_multivariateGaussian m N hN, Matrix.det_smul,
    log_mul (pow_pos ht _).ne' hN.det_pos.ne', log_pow, add_div]
  have hd : (Fintype.card ι : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  rw [mul_div_cancel_left₀ _ hd, exp_add, exp_log ht]

lemma entropyPower_gaussianMixtureMeasure_map_matrix
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N A : Matrix ι ι ℝ)
    (hN : N.PosDef) (hA : A.det ≠ 0) :
    entropyPower (gaussianMixtureMeasure w (fun a ↦ A.toEuclideanLin (m a))
      (A * N * A.transpose)) =
        exp (2 * log |A.det| / (Fintype.card ι : ℝ)) * entropyPower (gaussianMixtureMeasure w m N) := by
  rw [entropyPower, entropyWith_gaussianMixtureMeasure_map_matrix w hw hw1 m N A hN hA,
    entropyPower, ← exp_add]
  congr 1
  ring

lemma entropyPower_multivariateGaussian_map_matrix
    (m : EuclideanSpace ℝ ι) (N A : Matrix ι ι ℝ) (hN : N.PosDef) (hA : A.det ≠ 0) :
    entropyPower (multivariateGaussian (A.toEuclideanLin m) (A * N * A.transpose)) =
      exp (2 * log |A.det| / (Fintype.card ι : ℝ)) * entropyPower (multivariateGaussian m N) := by
  simpa only [gaussianMixtureMeasure, Fintype.sum_unique, ENNReal.ofReal_one, one_smul] using
    entropyPower_gaussianMixtureMeasure_map_matrix (fun _ : Unit ↦ 1)
      (fun _ ↦ zero_le_one) (by simp) (fun _ ↦ m) N A hN hA

lemma exists_gaussian_whitening_matrix (D : Matrix ι ι ℝ) (hD : D.PosDef) :
    ∃ A : Matrix ι ι ℝ, A.det ≠ 0 ∧ A * D * A.transpose = 1 := by
  let R := CFC.sqrt D
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)
  have hRdet : R.det ≠ 0 := (det_covarianceSqrt_pos hD).ne'
  have hRt : R.transpose = R := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hRit : R⁻¹.transpose = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRt]
  have hRR : R * R = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using inv_ne_zero hRdet
  · rw [hRit, ← hRR]
    calc
      R⁻¹ * (R * R) * R⁻¹ = (R⁻¹ * R) * (R * R⁻¹) := by noncomm_ring
      _ = 1 := by rw [Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hRdet),
        Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hRdet), one_mul]

/-- Stam's inequality for the entropy and Fisher information of a native finite mixture. -/
theorem entropyPower_mul_traceFisherWith_gaussianMixtureMeasure_ge [Nonempty ι]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) :
    (Fintype.card ι : ℝ) ≤ entropyPower (gaussianMixtureMeasure w m N) *
      traceFisherWith volume (gaussianMixturePDFReal w m N) := by
  let H := fun t : ℝ ↦ entropyWith
    (gaussianMixtureMeasure w m (N + t • (1 : Matrix ι ι ℝ))) volume
  let J := fun t : ℝ ↦ traceFisherWith volume
    (gaussianMixturePDFReal w m (N + t • (1 : Matrix ι ι ℝ)))
  have hderiv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt H (J t / 2) t := by
    convert hasDerivAt_entropyWith_gaussianMixtureMeasure_add_isotropic w hw hw1 m N hN ht
      using 1
    dsimp only [J, traceFisherWith]
    ring
  have hJ : 0 ≤ J 0 := by
    simp only [J, zero_smul, add_zero]
    exact traceFisherWith_nonneg volume _
      (fun x ↦ (gaussianMixturePDFReal_pos w hw hw1 m N hN x).le)
  have hbound (t : ℝ) (ht : 0 < t) :
      J t ≤ (Fintype.card ι : ℝ) * J 0 / ((Fintype.card ι : ℝ) + t * J 0) := by
    simpa only [J, zero_smul, add_zero] using
      traceFisherWith_gaussianMixture_add_isotropic_le_optimized w hw hw1 m N hN ht
  have h := entropy_power_mul_fisher_ge_of_heat_flow H J
    (Nat.cast_pos.mpr Fintype.card_pos) hJ hderiv hbound
    (tendsto_entropyWith_gaussianMixtureMeasure_add_isotropic_sub_log w hw hw1 m N hN)
  simpa only [H, J, zero_smul, add_zero, entropyPower] using h

/-- Adding isotropic Gaussian noise increases native mixture entropy power by its variance. -/
theorem entropyPower_gaussianMixtureMeasure_add_isotropic [Nonempty ι]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    entropyPower (gaussianMixtureMeasure w m N) + t ≤
      entropyPower (gaussianMixtureMeasure w m (N + t • (1 : Matrix ι ι ℝ))) := by
  let H := fun t : ℝ ↦ entropyWith
    (gaussianMixtureMeasure w m (N + t • (1 : Matrix ι ι ℝ))) volume
  let J := fun t : ℝ ↦ traceFisherWith volume
    (gaussianMixturePDFReal w m (N + t • (1 : Matrix ι ι ℝ)))
  have hderiv (s : ℝ) (hs : 0 ≤ s) : HasDerivAt H (J s / 2) s := by
    convert hasDerivAt_entropyWith_gaussianMixtureMeasure_add_isotropic w hw hw1 m N hN hs
      using 1
    dsimp only [J, traceFisherWith]
    ring
  have hstam (s : ℝ) (hs : 0 ≤ s) :
      (Fintype.card ι : ℝ) ≤ exp (2 * H s / (Fintype.card ι : ℝ) -
        (log (2 * π) + 1)) * J s :=
    entropyPower_mul_traceFisherWith_gaussianMixtureMeasure_ge w hw hw1 m _
      (hN.add_posSemidef (PosDef.one.posSemidef.smul hs))
  have h := entropy_power_add_le_of_heat_flow H J (Nat.cast_pos.mpr Fintype.card_pos)
    hderiv hstam ht
  simpa only [H, zero_smul, add_zero, entropyPower] using h

/-- The Gaussian-increment entropy-power inequality for native finite Gaussian mixtures. -/
theorem entropyPower_gaussianMixtureMeasure_add [Nonempty ι]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N D : Matrix ι ι ℝ)
    (hN : N.PosDef) (hD : D.PosDef) :
    entropyPower (gaussianMixtureMeasure w m N) +
        entropyPower (multivariateGaussian (0 : EuclideanSpace ℝ ι) D) ≤
      entropyPower (gaussianMixtureMeasure w m (N + D)) := by
  obtain ⟨A, hA, hAD⟩ := exists_gaussian_whitening_matrix D hD
  have h := entropyPower_gaussianMixtureMeasure_add_isotropic w hw hw1
    (fun a ↦ A.toEuclideanLin (m a)) (A * N * A.transpose)
    (posDef_covariance_congruence N A hN hA) (t := 1) zero_le_one
  have hcov : A * N * A.transpose + 1 = A * (N + D) * A.transpose := by
    rw [Matrix.mul_add, Matrix.add_mul, hAD]
  simp only [one_smul, hcov] at h
  rw [entropyPower_gaussianMixtureMeasure_map_matrix w hw hw1 m N A hN hA,
    entropyPower_gaussianMixtureMeasure_map_matrix w hw hw1 m (N + D) A (hN.add hD) hA] at h
  have hg := entropyPower_multivariateGaussian_map_matrix
    (0 : EuclideanSpace ℝ ι) D A hD hA
  simp only [map_zero, hAD] at hg
  have hunit : entropyPower (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (1 : Matrix ι ι ℝ)) = 1 := by
    simpa only [one_smul] using
      entropyPower_multivariateGaussian_isotropic (0 : EuclideanSpace ℝ ι) zero_lt_one
  rw [hunit] at hg
  rw [hg, ← mul_add] at h
  exact le_of_mul_le_mul_left h (exp_pos _)

/-- The Gaussian-increment inequality without the conventional entropy-power normalization. -/
theorem exp_entropyWith_gaussianMixtureMeasure_add [Nonempty ι]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N D : Matrix ι ι ℝ)
    (hN : N.PosDef) (hD : D.PosDef) :
    exp (2 * entropyWith (gaussianMixtureMeasure w m N) volume / (Fintype.card ι : ℝ)) +
        exp (2 * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) D) volume /
          (Fintype.card ι : ℝ)) ≤
      exp (2 * entropyWith (gaussianMixtureMeasure w m (N + D)) volume /
        (Fintype.card ι : ℝ)) := by
  have h := entropyPower_gaussianMixtureMeasure_add w hw hw1 m N D hN hD
  simp only [entropyPower, exp_sub] at h
  rw [← add_div] at h
  exact (div_le_div_iff_of_pos_right (exp_pos _)).mp h

end CapacityAtlas.MeasureInformation
