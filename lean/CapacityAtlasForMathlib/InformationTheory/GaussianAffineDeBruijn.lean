/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianFisherBasis
import Mathlib.Algebra.Order.Field.Pi
import CapacityAtlasForMathlib.Analysis.Matrix.CovarianceDiagonalization

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped BigOperators Topology

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem hasDerivAt_entropyWith_gaussianMixtureMeasure_diagonal_add
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ entropyWith
      (gaussianMixtureMeasure w m (diagonal (fun i ↦ c i + s))) volume)
      ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t))) (EuclideanSpace.single i 1)) t := by
  apply (hasDerivAt_entropyWith_gaussianMixture_diagonal_add w hw hw1 m c hc ht).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [gaussianMixtureMeasure_eq_withDensity w hw m _
    (PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) hs))]

/-- Positivity at the evaluation time gives a two-sided entropy derivative. -/
theorem hasDerivAt_entropyWith_gaussianMixtureMeasure_diagonal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) {t : ℝ}
    (ht : ∀ i, 0 < c i + t) :
    HasDerivAt (fun s ↦ entropyWith
      (gaussianMixtureMeasure w m (diagonal (fun i ↦ c i + s))) volume)
      ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t))) (EuclideanSpace.single i 1)) t := by
  obtain ⟨ε, hε, hbound⟩ := Pi.exists_forall_pos_add_lt ht
  have hc (i : ι) : 0 ≤ c i + t - ε := by simpa only [zero_add] using (sub_nonneg.mpr (hbound i).le)
  have hd := (hasDerivAt_entropyWith_gaussianMixtureMeasure_diagonal_add w hw hw1 m
    (fun i ↦ c i + t - ε) hc hε).comp_of_eq t
      (((hasDerivAt_id t).sub_const t).add_const ε) (by simp)
  have hcov (s : ℝ) : (fun i ↦ c i + t - ε + (s - t + ε)) = fun i ↦ c i + s := by
    funext i; ring
  simp only [mul_one] at hd
  convert! hd using 1
  · funext s
    simp only [Function.comp_apply, id_eq, hcov]
  · simp only [sub_add_cancel]

/-- Invertible affine transport preserves the entropy derivative of a covariance flow. -/
theorem hasDerivAt_entropyWith_gaussianMixtureMeasure_congruence_diagonal_add
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ entropyWith
      (gaussianMixtureMeasure w (fun a ↦ A.toEuclideanLin (m a))
        (A * diagonal (fun i ↦ c i + s) * A.transpose)) volume)
      ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t))) (EuclideanSpace.single i 1)) t := by
  apply ((hasDerivAt_entropyWith_gaussianMixtureMeasure_diagonal_add w hw hw1 m c hc ht).add_const
    (log |A.det|)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact entropyWith_gaussianMixtureMeasure_map_matrix w hw hw1 m _ A
    (PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) hs)) hA

theorem hasDerivAt_entropyWith_gaussianMixtureMeasure_congruence_diagonal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ)
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) {t : ℝ} (ht : ∀ i, 0 < c i + t) :
    HasDerivAt (fun s ↦ entropyWith
      (gaussianMixtureMeasure w (fun a ↦ A.toEuclideanLin (m a))
        (A * diagonal (fun i ↦ c i + s) * A.transpose)) volume)
      ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t))) (EuclideanSpace.single i 1)) t := by
  apply ((hasDerivAt_entropyWith_gaussianMixtureMeasure_diagonal w hw hw1 m c ht).add_const
    (log |A.det|)).congr_of_eventuallyEq
  have hpos : ∀ᶠ s in 𝓝 t, ∀ i, 0 < c i + s := by
    apply eventually_all.mpr
    intro i
    exact (tendsto_const_nhds.add tendsto_id).eventually (eventually_gt_nhds (ht i))
  filter_upwards [hpos] with s hs
  exact entropyWith_gaussianMixtureMeasure_map_matrix w hw hw1 m _ A (PosDef.diagonal hs) hA

/-- Native de Bruijn identity with positive initial covariance, including at time zero. -/
theorem hasDerivAt_entropyWith_gaussianMixtureMeasure_add_isotropic
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s ↦ entropyWith
      (gaussianMixtureMeasure w m (N + s • (1 : Matrix ι ι ℝ))) volume)
      ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (N + t • (1 : Matrix ι ι ℝ))) (EuclideanSpace.single i 1)) t := by
  let U : Matrix ι ι ℝ := hN.isHermitian.eigenvectorUnitary
  let c := hN.isHermitian.eigenvalues
  let m' := fun a ↦ U.transpose.toEuclideanLin (m a)
  have hU : U * U.transpose = 1 := by
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hN.isHermitian.eigenvectorUnitary
  have hUdet : U.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det U).mp Unitary.isUnit_coe)
  have hspectral : N = U * diagonal c * U.transpose := by
    simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq] using hN.isHermitian.spectral_theorem
  have hcov (s : ℝ) : N + s • (1 : Matrix ι ι ℝ) =
      U * diagonal (fun i ↦ c i + s) * U.transpose := by
    have hd : diagonal (fun i ↦ c i + s) = diagonal c + s • (1 : Matrix ι ι ℝ) := by
      rw [← diagonal_add, ← Matrix.diagonal_one, ← diagonal_smul]
      simp only [Pi.smul_def, smul_eq_mul, mul_one]
    rw [hd, Matrix.mul_add, Matrix.add_mul, ← hspectral, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
  have hm : (fun a ↦ U.toEuclideanLin (m' a)) = m := by
    funext a
    change Matrix.toEuclideanCLM (𝕜 := ℝ) U
      (Matrix.toEuclideanCLM (𝕜 := ℝ) U.transpose (m a)) = m a
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul, hU, map_one]
    rfl
  have hct (i : ι) : 0 < c i + t := add_pos_of_pos_of_nonneg (hN.eigenvalues_pos i) ht
  have hNt : (N + t • (1 : Matrix ι ι ℝ)).PosDef :=
    hN.add_posSemidef (PosDef.one.posSemidef.smul ht)
  have h := hasDerivAt_entropyWith_gaussianMixtureMeasure_congruence_diagonal
    w hw hw1 m' c U hUdet hct
  simp only [hm, ← hcov] at h
  apply h.congr_deriv
  have hdir (i : ι) : U.toEuclideanLin (EuclideanSpace.single i 1) = hN.isHermitian.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    exact congrFun (hN.isHermitian.eigenvectorUnitary_mulVec i) j
  calc
    _ = (1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (N + t • (1 : Matrix ι ι ℝ)))
          (hN.isHermitian.eigenvectorBasis i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hf := directionalFisherWith_gaussianMixturePDFReal_matrix w hw hw1 m'
        (diagonal (fun i ↦ c i + t)) U (PosDef.diagonal hct) hUdet (EuclideanSpace.single i 1)
      simpa only [hm, ← hcov, hdir] using hf.symm
    _ = _ := by
      congr 1
      simpa only [EuclideanSpace.basisFun_apply] using
        sum_directionalFisherWith_gaussianMixturePDFReal_basis w hw hw1 m _ hNt
          hN.isHermitian.eigenvectorBasis (EuclideanSpace.basisFun ι ℝ)

/-- Every positive covariance direction admits an exact native entropy derivative. -/
theorem exists_hasDerivAt_entropyWith_gaussianMixtureMeasure_affine
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N D : Matrix ι ι ℝ)
    (hN : N.PosSemidef) (hD : D.PosDef) :
    ∃ (A : Matrix ι ι ℝ) (c : ι → ℝ),
      A.det ≠ 0 ∧ (∀ i, 0 ≤ c i) ∧
      (∀ s : ℝ, N + s • D = A * diagonal (fun i ↦ c i + s) * A.transpose) ∧
      ∀ t : ℝ, 0 < t → HasDerivAt
        (fun s ↦ entropyWith (gaussianMixtureMeasure w m (N + s • D)) volume)
        ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
          (gaussianMixturePDFReal w (fun a ↦ A⁻¹.toEuclideanLin (m a))
            (diagonal (fun i ↦ c i + t))) (EuclideanSpace.single i 1)) t := by
  obtain ⟨A, c, hA, hc, hcov⟩ := exists_diagonalization_covariance_affine N D hN hD
  refine ⟨A, c, hA, hc, hcov, ?_⟩
  intro t ht
  have hm : (fun a ↦ A.toEuclideanLin (A⁻¹.toEuclideanLin (m a))) = m := by
    funext a
    change Matrix.toEuclideanCLM (𝕜 := ℝ) A
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (m a)) = m a
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), map_one]
    rfl
  have h := hasDerivAt_entropyWith_gaussianMixtureMeasure_congruence_diagonal_add
    w hw hw1 (fun a ↦ A⁻¹.toEuclideanLin (m a)) c hc A hA ht
  simpa only [hm, ← hcov] using h

end CapacityAtlas.MeasureInformation
