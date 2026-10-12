/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDeBruijn

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

lemma abs_weighted_average_le_sum_abs (a s : α → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hpos : 0 < ∑ k, a k) :
    |(∑ k, a k * s k) / ∑ k, a k| ≤ ∑ k, |s k| := by
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc
    _ ≤ ∑ k, |a k * s k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, a k * |s k| := by simp only [abs_mul, abs_of_nonneg (ha _)]
    _ ≤ ∑ k, a k * (∑ i, |s i|) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun i _ ↦ abs_nonneg (s i)) (Finset.mem_univ k)) (ha k)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

lemma directionalScore_gaussianMixturePDFReal (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (v x : EuclideanSpace ℝ ι) :
    directionalScore (gaussianMixturePDFReal w m N) v x =
      (∑ k, (w k * multivariateGaussianPDFReal (m k) N x) *
        (-(v ⬝ᵥ N⁻¹ *ᵥ (x - m k)))) / gaussianMixturePDFReal w m N x := by
  rw [directionalScore, lineDeriv_gaussianMixturePDFReal_eq_sum w m N hN]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [(hasLineDerivAt_multivariateGaussianPDFReal (m k) x v N hN).lineDeriv]
  ring

lemma abs_directionalScore_gaussianMixturePDFReal_le
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v x : EuclideanSpace ℝ ι) :
    |directionalScore (gaussianMixturePDFReal w m N) v x| ≤
      ∑ k, |v ⬝ᵥ N⁻¹ *ᵥ (x - m k)| := by
  rw [directionalScore_gaussianMixturePDFReal w m N hN]
  simpa only [abs_neg, gaussianMixturePDFReal] using abs_weighted_average_le_sum_abs
    (fun k ↦ w k * multivariateGaussianPDFReal (m k) N x)
    (fun k ↦ -(v ⬝ᵥ N⁻¹ *ᵥ (x - m k)))
    (fun k ↦ mul_nonneg (hw k) (multivariateGaussianPDFReal_pos (m k) N hN x).le)
    (gaussianMixturePDFReal_pos w hw hw1 m N hN x)

@[fun_prop]
lemma measurable_directionalScore_gaussianMixturePDFReal (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) :
    Measurable (directionalScore (gaussianMixturePDFReal w m N) v) := by
  change Measurable (fun x ↦ directionalScore (gaussianMixturePDFReal w m N) v x)
  simp_rw [directionalScore_gaussianMixturePDFReal w m N hN]
  apply Measurable.div _ (measurable_gaussianMixturePDFReal w m N)
  simp only [dotProduct, Matrix.mulVec, Pi.sub_apply]
  fun_prop

lemma memLp_gaussian_directional_score (m v k : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ v ⬝ᵥ N⁻¹ *ᵥ (x - m)) p
      (multivariateGaussian k S) := by
  simp_rw [Matrix.dotProduct_mulVec]
  simp only [dotProduct, Pi.sub_apply]
  apply memLp_finsetSum
  intro i _
  have hi : MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) p (multivariateGaussian k S) := by
    simpa only [id_eq, EuclideanSpace.coe_proj] using
      (IsGaussian.memLp_id (multivariateGaussian k S) p hp).continuousLinearMap_comp
        (EuclideanSpace.proj (𝕜 := ℝ) i)
  exact (hi.sub (memLp_const (m i))).const_mul _

/-- Every finite Gaussian-mixture score has all finite moments under any native Gaussian law. -/
theorem memLp_directionalScore_gaussianMixturePDFReal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v k : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (directionalScore (gaussianMixturePDFReal w m N) v) p
      (multivariateGaussian k S) := by
  have hbound : MemLp (fun x : EuclideanSpace ℝ ι ↦ ∑ a, |v ⬝ᵥ N⁻¹ *ᵥ (x - m a)|) p
      (multivariateGaussian k S) :=
    memLp_finsetSum _ (fun a _ ↦ (memLp_gaussian_directional_score (m a) v k N S p hp).abs)
  apply hbound.mono' (measurable_directionalScore_gaussianMixturePDFReal w m N hN v).aestronglyMeasurable
  filter_upwards with x
  exact (Real.norm_eq_abs _).trans_le
    (abs_directionalScore_gaussianMixturePDFReal_le w hw hw1 m N hN v x)

lemma secondDeriv_div_gaussianMixturePDFReal (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (v x : EuclideanSpace ℝ ι) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v) x v /
      gaussianMixturePDFReal w m N x =
        (∑ k, (w k * multivariateGaussianPDFReal (m k) N x) *
          ((v ⬝ᵥ N⁻¹ *ᵥ (x - m k)) ^ 2 - v ⬝ᵥ N⁻¹ *ᵥ v)) /
            gaussianMixturePDFReal w m N x := by
  congr 1
  change lineDeriv ℝ (fun y ↦ lineDeriv ℝ
    (fun z ↦ ∑ a, w a * multivariateGaussianPDFReal (m a) N z) y v) x v = _
  rw [lineDeriv_lineDeriv_gaussian_mixture w m N hN]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hasLineDerivAt_lineDeriv_multivariateGaussianPDFReal (m k) x v N hN).lineDeriv]
  ring

lemma hasLineDerivAt_directionalScore_gaussianMixturePDFReal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v x : EuclideanSpace ℝ ι) :
    HasLineDerivAt ℝ (directionalScore (gaussianMixturePDFReal w m N) v)
      (lineDeriv ℝ (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v) x v /
        gaussianMixturePDFReal w m N x -
          directionalScore (gaussianMixturePDFReal w m N) v x ^ 2) x v := by
  have hfirst := hasLineDerivAt_gaussianMixturePDFReal w m N hN x v
  have hsecond := hasLineDerivAt_lineDeriv_gaussianMixturePDFReal w m N hN x v
  have hpos := gaussianMixturePDFReal_pos w hw hw1 m N hN x
  unfold HasLineDerivAt at hfirst hsecond ⊢
  convert! hsecond.div hfirst (by simpa only [zero_smul, add_zero] using hpos.ne') using 1
  simp only [directionalScore, zero_smul, add_zero]
  field_simp

@[fun_prop]
lemma measurable_secondDeriv_div_gaussianMixturePDFReal (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) :
    Measurable (fun x ↦ lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v) x v /
        gaussianMixturePDFReal w m N x) := by
  simp_rw [secondDeriv_div_gaussianMixturePDFReal w m N hN]
  apply Measurable.div _ (measurable_gaussianMixturePDFReal w m N)
  simp only [dotProduct, Matrix.mulVec, Pi.sub_apply]
  fun_prop

lemma memLp_two_secondDeriv_div_gaussianMixturePDFReal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v k : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    MemLp (fun x ↦ lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v) x v /
        gaussianMixturePDFReal w m N x) 2 (multivariateGaussian k S) := by
  have hc : MemLp (fun _ : EuclideanSpace ℝ ι ↦ v ⬝ᵥ N⁻¹ *ᵥ v) 2
      (multivariateGaussian k S) := memLp_const _
  have hbound : MemLp (fun x : EuclideanSpace ℝ ι ↦
      ∑ a, |(v ⬝ᵥ N⁻¹ *ᵥ (x - m a)) ^ 2 - v ⬝ᵥ N⁻¹ *ᵥ v|) 2
        (multivariateGaussian k S) :=
    memLp_finsetSum _ (fun a _ ↦ ((memLp_two_sq_gaussian_directional_score (m a) v k N S).sub hc).abs)
  apply hbound.mono' (measurable_secondDeriv_div_gaussianMixturePDFReal w m N hN v).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, secondDeriv_div_gaussianMixturePDFReal w m N hN]
  exact abs_weighted_average_le_sum_abs
    (fun a ↦ w a * multivariateGaussianPDFReal (m a) N x)
    (fun a ↦ (v ⬝ᵥ N⁻¹ *ᵥ (x - m a)) ^ 2 - v ⬝ᵥ N⁻¹ *ᵥ v)
    (fun a ↦ mul_nonneg (hw a) (multivariateGaussianPDFReal_pos (m a) N hN x).le)
    (gaussianMixturePDFReal_pos w hw hw1 m N hN x)

/-- The actual score derivative is square-integrable under every Gaussian law. -/
theorem memLp_two_lineDeriv_directionalScore_gaussianMixturePDFReal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v k : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    MemLp (fun x ↦ lineDeriv ℝ (directionalScore (gaussianMixturePDFReal w m N) v) x v) 2
      (multivariateGaussian k S) := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hs := memLp_directionalScore_gaussianMixturePDFReal w hw hw1 m N hN v k S 4 (by norm_num)
  have hsq : MemLp (fun x ↦ directionalScore (gaussianMixturePDFReal w m N) v x ^ 2) 2
      (multivariateGaussian k S) := by
    simpa only [pow_two] using hs.mul' hs
  simp_rw [(hasLineDerivAt_directionalScore_gaussianMixturePDFReal w hw hw1 m N hN v _).lineDeriv]
  exact (memLp_two_secondDeriv_div_gaussianMixturePDFReal w hw hw1 m N hN v k S).sub hsq

@[fun_prop]
lemma measurable_lineDeriv_directionalScore_gaussianMixturePDFReal
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ ι) :
    Measurable (fun x ↦ lineDeriv ℝ (directionalScore (gaussianMixturePDFReal w m N) v) x v) := by
  simp_rw [(hasLineDerivAt_directionalScore_gaussianMixturePDFReal w hw hw1 m N hN v _).lineDeriv]
  exact (measurable_secondDeriv_div_gaussianMixturePDFReal w m N hN v).sub
    ((measurable_directionalScore_gaussianMixturePDFReal w m N hN v).pow_const 2)

end CapacityAtlas.MeasureInformation
