/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianScoreIntegration

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

lemma memLp_comp_add_gaussianMixture (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (n : EuclideanSpace ℝ ι) (N S : Matrix ι ι ℝ) (hN : N.PosSemidef) (hS : S.PosSemidef)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : Measurable f) {p : ℝ≥0∞}
    (hLp : MemLp f p (gaussianMixtureMeasure w (fun a ↦ m a + n) (N + S))) :
    MemLp (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ f (z.1 + z.2)) p
      ((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S)) := by
  rw [← gaussianMixtureMeasure_conv w m n N S hN hS] at hLp
  exact (memLp_map_measure_iff hf.aestronglyMeasurable measurable_add.aemeasurable).mp hLp

lemma integral_comp_add_gaussianMixture (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (n : EuclideanSpace ℝ ι) (N S : Matrix ι ι ℝ) (hN : N.PosSemidef) (hS : S.PosSemidef)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : Measurable f) :
    (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, f (z.1 + z.2)
      ∂((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S))) =
        ∫ x, f x ∂gaussianMixtureMeasure w (fun a ↦ m a + n) (N + S) := by
  rw [← gaussianMixtureMeasure_conv w m n N S hN hS, Measure.conv,
    integral_map measurable_add.aemeasurable hf.aestronglyMeasurable]

lemma integral_score_fst_mul_sum_gaussianMixture
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (n v : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) (hN : N.PosDef) (hS : S.PosDef) :
    (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      directionalScore (gaussianMixturePDFReal w m N) v z.1 *
        directionalScore (gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)) v (z.1 + z.2)
      ∂((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S))) =
        directionalFisherWith volume (gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)) v := by
  let q := gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)
  let C := directionalScore q v
  let C' := fun x ↦ lineDeriv ℝ C x v
  have hNS := hN.add hS
  have hCm : Measurable C := measurable_directionalScore_gaussianMixturePDFReal w _ _ hNS v
  have hC'm : Measurable C' :=
    measurable_lineDeriv_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v
  have hC : MemLp C 2 (gaussianMixtureMeasure w (fun a ↦ m a + n) (N + S)) :=
    memLp_two_gaussianMixtureMeasure hCm (fun a ↦
      memLp_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v _ _ 2 (by norm_num))
  have hC' : MemLp C' 2 (gaussianMixtureMeasure w (fun a ↦ m a + n) (N + S)) :=
    memLp_two_gaussianMixtureMeasure hC'm (fun a ↦
      memLp_two_lineDeriv_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v _ _)
  have hsum := memLp_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef hCm hC
  have hsum' := memLp_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef hC'm hC'
  have hA : MemLp (directionalScore (gaussianMixturePDFReal w m N) v) 2
      (gaussianMixtureMeasure w m N) :=
    memLp_two_gaussianMixtureMeasure (measurable_directionalScore_gaussianMixturePDFReal w m N hN v)
      (fun a ↦ memLp_directionalScore_gaussianMixturePDFReal w hw hw1 m N hN v _ _ 2 (by norm_num))
  have hint := (hA.comp_fst (multivariateGaussian n S)).integrable_mul hsum
  have hint' := hsum'.integrable (by norm_num)
  change (∫ z, directionalScore (gaussianMixturePDFReal w m N) v z.1 * C (z.1 + z.2)
    ∂((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S))) = _
  rw [integral_prod_symm (fun z ↦ directionalScore (gaussianMixturePDFReal w m N) v z.1 *
    C (z.1 + z.2)) hint]
  calc
    _ = ∫ y, -(∫ x, C' (x + y) ∂gaussianMixtureMeasure w m N)
        ∂multivariateGaussian n S := by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_directionalScore_mul_gaussianMixture w hw hw1 m N hN v
      · intro x
        have hd := (hasLineDerivAt_directionalScore_gaussianMixturePDFReal
          w hw hw1 (fun a ↦ m a + n) (N + S) hNS v (x + y)).lineDifferentiableAt.hasLineDerivAt
        simpa only [C, C', q, HasLineDerivAt, add_assoc, add_left_comm, add_comm] using hd
      · intro a
        exact memLp_comp_add_const_multivariateGaussian hCm (m a) y N
          (memLp_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v _ _ 2 (by norm_num))
      · intro a
        exact (memLp_comp_add_const_multivariateGaussian hC'm (m a) y N
          (memLp_two_lineDeriv_directionalScore_gaussianMixturePDFReal
            w hw hw1 _ _ hNS v _ _)).integrable (by norm_num)
    _ = -(∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, C' (z.1 + z.2)
        ∂((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S))) := by
      rw [integral_neg, integral_prod_symm _ hint']
    _ = _ := by
      rw [integral_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef C' hC'm,
        integral_lineDeriv_directionalScore_gaussianMixture w hw hw1 _ _ hNS v, neg_neg]

lemma integral_score_snd_mul_sum_gaussianMixture
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (n v : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) (hN : N.PosDef) (hS : S.PosDef) :
    (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      directionalScore (multivariateGaussianPDFReal n S) v z.2 *
        directionalScore (gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)) v (z.1 + z.2)
      ∂((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S))) =
        directionalFisherWith volume (gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)) v := by
  let q := gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)
  let C := directionalScore q v
  let C' := fun x ↦ lineDeriv ℝ C x v
  have hNS := hN.add hS
  have hCm : Measurable C := measurable_directionalScore_gaussianMixturePDFReal w _ _ hNS v
  have hC'm : Measurable C' :=
    measurable_lineDeriv_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v
  have hC : MemLp C 2 (gaussianMixtureMeasure w (fun a ↦ m a + n) (N + S)) :=
    memLp_two_gaussianMixtureMeasure hCm (fun a ↦
      memLp_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v _ _ 2 (by norm_num))
  have hC' : MemLp C' 2 (gaussianMixtureMeasure w (fun a ↦ m a + n) (N + S)) :=
    memLp_two_gaussianMixtureMeasure hC'm (fun a ↦
      memLp_two_lineDeriv_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v _ _)
  have hsum := memLp_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef hCm hC
  have hsum' := memLp_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef hC'm hC'
  have hB := memLp_directionalScore_multivariateGaussianPDFReal n v n S S hS 2 (by norm_num)
  have hint := (hB.comp_snd (gaussianMixtureMeasure w m N)).integrable_mul hsum
  have hint' := hsum'.integrable (by norm_num)
  change (∫ z, directionalScore (multivariateGaussianPDFReal n S) v z.2 * C (z.1 + z.2)
    ∂((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S))) = _
  rw [integral_prod (fun z ↦ directionalScore (multivariateGaussianPDFReal n S) v z.2 *
    C (z.1 + z.2)) hint]
  calc
    _ = ∫ x, -(∫ y, C' (x + y) ∂multivariateGaussian n S)
        ∂gaussianMixtureMeasure w m N := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_directionalScore_mul_multivariateGaussian n S hS v
      · intro y
        have hd := (hasLineDerivAt_directionalScore_gaussianMixturePDFReal
          w hw hw1 (fun a ↦ m a + n) (N + S) hNS v (x + y)).lineDifferentiableAt.hasLineDerivAt
        simpa only [C, C', q, HasLineDerivAt, add_assoc, add_left_comm, add_comm] using hd
      · simpa only [add_comm] using memLp_comp_add_const_multivariateGaussian hCm n x S
          (memLp_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v _ _ 2 (by norm_num))
      · have hi := (memLp_comp_add_const_multivariateGaussian hC'm n x S
          (memLp_two_lineDeriv_directionalScore_gaussianMixturePDFReal
            w hw hw1 _ _ hNS v _ _)).integrable (by norm_num)
        simpa only [add_comm] using hi
    _ = -(∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, C' (z.1 + z.2)
        ∂((gaussianMixtureMeasure w m N).prod (multivariateGaussian n S))) := by
      rw [integral_neg, integral_prod _ hint']
    _ = _ := by
      rw [integral_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef C' hC'm,
        integral_lineDeriv_directionalScore_gaussianMixture w hw hw1 _ _ hNS v, neg_neg]

lemma integral_sq_linear_combination {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (a b : ℝ) :
    (∫ x, (a * f x + b * g x) ^ 2 ∂μ) =
      a ^ 2 * (∫ x, f x ^ 2 ∂μ) + (2 * a * b) * (∫ x, f x * g x ∂μ) +
        b ^ 2 * (∫ x, g x ^ 2 ∂μ) := by
  have heq : (fun x ↦ (a * f x + b * g x) ^ 2) =
      fun x ↦ (a ^ 2 * f x ^ 2 + (2 * a * b) * (f x * g x)) + b ^ 2 * g x ^ 2 := by
    ext x
    ring
  rw [heq, integral_add
    (f := fun x ↦ a ^ 2 * f x ^ 2 + (2 * a * b) * (f x * g x))
    (g := fun x ↦ b ^ 2 * g x ^ 2)
    ((hf.integrable_sq.const_mul _).add ((hf.integrable_mul hg).const_mul _))
    (hg.integrable_sq.const_mul _),
    integral_add (f := fun x ↦ a ^ 2 * f x ^ 2)
      (g := fun x ↦ (2 * a * b) * (f x * g x))
      (hf.integrable_sq.const_mul _) ((hf.integrable_mul hg).const_mul _)]
  simp only [integral_const_mul]

lemma integral_sq_le_of_score_correlations {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B C : Ω → ℝ) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hC : MemLp C 2 μ)
    (hAB : (∫ x, A x * B x ∂μ) = 0)
    (hAC : (∫ x, A x * C x ∂μ) = ∫ x, C x ^ 2 ∂μ)
    (hBC : (∫ x, B x * C x ∂μ) = ∫ x, C x ^ 2 ∂μ) (u : ℝ) :
    (∫ x, C x ^ 2 ∂μ) ≤
      u ^ 2 * (∫ x, A x ^ 2 ∂μ) + (1 - u) ^ 2 * (∫ x, B x ^ 2 ∂μ) := by
  let U := fun x ↦ u * A x + (1 - u) * B x
  have hU : MemLp U 2 μ := (hA.const_mul u).add (hB.const_mul (1 - u))
  have hUC : (∫ x, U x * C x ∂μ) = ∫ x, C x ^ 2 ∂μ := by
    simp only [U, add_mul, mul_assoc]
    rw [integral_add (f := fun x ↦ u * (A x * C x))
      (g := fun x ↦ (1 - u) * (B x * C x)) ((hA.integrable_mul hC).const_mul u)
      ((hB.integrable_mul hC).const_mul (1 - u)), integral_const_mul,
      integral_const_mul, hAC, hBC]
    ring
  have hU2 : (∫ x, U x ^ 2 ∂μ) =
      u ^ 2 * (∫ x, A x ^ 2 ∂μ) + (1 - u) ^ 2 * (∫ x, B x ^ 2 ∂μ) := by
    rw [integral_sq_linear_combination μ A B hA hB u (1 - u), hAB, mul_zero, add_zero]
  have hnonneg : 0 ≤ ∫ x, (1 * U x + (-1) * C x) ^ 2 ∂μ :=
    integral_nonneg (fun x ↦ sq_nonneg _)
  rw [integral_sq_linear_combination μ U C hU hC 1 (-1), hUC, hU2] at hnonneg
  nlinarith

/-- Directional Fisher contraction for a finite native Gaussian mixture plus Gaussian noise. -/
theorem directionalFisherWith_gaussianMixture_add_le
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (n v : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) (hN : N.PosDef) (hS : S.PosDef) (u : ℝ) :
    directionalFisherWith volume (gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)) v ≤
      u ^ 2 * directionalFisherWith volume (gaussianMixturePDFReal w m N) v +
        (1 - u) ^ 2 * (v ⬝ᵥ S⁻¹ *ᵥ v) := by
  let μ := gaussianMixtureMeasure w m N
  let ν := multivariateGaussian n S
  let A := directionalScore (gaussianMixturePDFReal w m N) v
  let B := directionalScore (multivariateGaussianPDFReal n S) v
  let C := directionalScore (gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)) v
  letI := isProbabilityMeasure_gaussianMixtureMeasure w hw hw1 m N
  have hNS := hN.add hS
  have hA : MemLp A 2 μ :=
    memLp_two_gaussianMixtureMeasure (measurable_directionalScore_gaussianMixturePDFReal w m N hN v)
      (fun a ↦ memLp_directionalScore_gaussianMixturePDFReal w hw hw1 m N hN v _ _ 2 (by norm_num))
  have hB : MemLp B 2 ν :=
    memLp_directionalScore_multivariateGaussianPDFReal n v n S S hS 2 (by norm_num)
  have hCm : Measurable C := measurable_directionalScore_gaussianMixturePDFReal w _ _ hNS v
  have hC : MemLp (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ C (z.1 + z.2)) 2
      (μ.prod ν) := memLp_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef hCm
        (memLp_two_gaussianMixtureMeasure hCm (fun a ↦
          memLp_directionalScore_gaussianMixturePDFReal w hw hw1 _ _ hNS v _ _ 2 (by norm_num)))
  have hA2 : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, A z.1 ^ 2 ∂μ.prod ν) =
      directionalFisherWith volume (gaussianMixturePDFReal w m N) v := by
    rw [integral_fun_fst (fun x ↦ A x ^ 2), probReal_univ, one_smul,
      directionalFisherWith_eq_gaussianMixtureMeasure w hw m N hN]
  have hB2 : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, B z.2 ^ 2 ∂μ.prod ν) =
      v ⬝ᵥ S⁻¹ *ᵥ v := by
    rw [integral_fun_snd (fun x ↦ B x ^ 2), probReal_univ, one_smul]
    simp_rw [B, directionalScore_multivariateGaussianPDFReal n v _ S hS, neg_sq,
      Matrix.dotProduct_mulVec]
    rw [integral_sq_dotProduct_sub_multivariateGaussian n S hS.posSemidef,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hS.det_pos.ne'), Matrix.one_mulVec,
      dotProduct_comm]
  have hC2 : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, C (z.1 + z.2) ^ 2 ∂μ.prod ν) =
      directionalFisherWith volume (gaussianMixturePDFReal w (fun a ↦ m a + n) (N + S)) v := by
    rw [integral_comp_add_gaussianMixture w m n N S hN.posSemidef hS.posSemidef
      (fun x ↦ C x ^ 2) (hCm.pow_const 2),
      directionalFisherWith_eq_gaussianMixtureMeasure w hw _ _ hNS]
  have hAB : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, A z.1 * B z.2 ∂μ.prod ν) = 0 := by
    rw [integral_prod_mul, integral_directionalScore_gaussianMixture w hw hw1 m N hN v, zero_mul]
  have hAC : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, A z.1 * C (z.1 + z.2)
      ∂μ.prod ν) = ∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, C (z.1 + z.2) ^ 2 ∂μ.prod ν := by
    rw [hC2]
    exact integral_score_fst_mul_sum_gaussianMixture w hw hw1 m n v N S hN hS
  have hBC : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, B z.2 * C (z.1 + z.2)
      ∂μ.prod ν) = ∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, C (z.1 + z.2) ^ 2 ∂μ.prod ν := by
    rw [hC2]
    exact integral_score_snd_mul_sum_gaussianMixture w hw hw1 m n v N S hN hS
  have h := integral_sq_le_of_score_correlations (μ.prod ν) (fun z ↦ A z.1) (fun z ↦ B z.2)
    (fun z ↦ C (z.1 + z.2)) (hA.comp_fst ν) (hB.comp_snd μ) hC hAB hAC hBC u
  rwa [hA2, hB2, hC2] at h

end CapacityAtlas.MeasureInformation
