/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianEntropyPower
import CapacityAtlasForMathlib.InformationTheory.GaussianProportionalEntropy
import CapacityAtlasForMathlib.LinearAlgebra.LogDetConcavity

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal MatrixOrder

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty ι]

/-- Proportional Gaussian covariances maximize the corresponding mixture entropy difference. -/
theorem entropyWith_gaussianMixtureMeasure_difference_le_of_proportional
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N M A B : Matrix ι ι ℝ)
    (hN : N.PosDef) (hB : B.PosDef)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hprop : A = a • B)
    (hdiff : M - N = B - A) :
    a * entropyWith (gaussianMixtureMeasure w m N) volume -
        entropyWith (gaussianMixtureMeasure w m M) volume ≤
      a * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) volume -
        entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) volume := by
  rcases eq_or_lt_of_le ha1 with heq | hlt
  · subst a
    simp only [one_smul] at hprop
    subst A
    have hNM : M = N := sub_eq_zero.mp (by simpa using hdiff)
    subst M
    simp
  · have hcov : M - N = (1 - a) • B := by rw [hdiff, sub_smul, one_smul, hprop]
    have hD : (M - N).PosDef := by
      rw [hcov]
      exact hB.smul (sub_pos.mpr hlt)
    have hsum : N + (M - N) = M := by abel
    have hEPI := entropyPower_gaussianMixtureMeasure_add w hw hw1 m N (M - N) hN hD
    rw [hsum] at hEPI
    have hpowerA : entropyPower (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) =
        a * entropyPower (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) := by
      rw [hprop, entropyPower_multivariateGaussian_smul _ B hB ha]
    have hpowerD : entropyPower (multivariateGaussian (0 : EuclideanSpace ℝ ι) (M - N)) =
        entropyPower (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) -
          entropyPower (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) := by
      rw [hcov, entropyPower_multivariateGaussian_smul _ _ hB (sub_pos.mpr hlt), hpowerA]
      ring
    rw [hpowerD] at hEPI
    have hlog := proportional_log_sub_le
      (entropyPower_pos (gaussianMixtureMeasure w m N))
      (entropyPower_pos (gaussianMixtureMeasure w m M))
      (entropyPower_pos (multivariateGaussian (0 : EuclideanSpace ℝ ι) A))
      (entropyPower_pos (multivariateGaussian (0 : EuclideanSpace ℝ ι) B))
      ha1 hpowerA hEPI
    simp only [entropyPower, log_exp] at hlog
    have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    have h := mul_le_mul_of_nonneg_right hlog hd.le
    field_simp at h
    nlinarith

theorem entropyWith_gaussianMixtureMeasure_weighted_difference_le_of_proportional
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N M A B : Matrix ι ι ℝ)
    (hN : N.PosDef) (hB : B.PosDef)
    {f g : ℝ} (hf : 0 < f) (hg : 0 < g) (hfg : f ≤ g)
    (hprop : A = (f / g) • B) (hdiff : M - N = B - A) :
    f * entropyWith (gaussianMixtureMeasure w m N) volume -
        g * entropyWith (gaussianMixtureMeasure w m M) volume ≤
      f * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) volume -
        g * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) volume := by
  have h := entropyWith_gaussianMixtureMeasure_difference_le_of_proportional
    w hw hw1 m N M A B hN hB (div_pos hf hg) ((div_le_one hg).mpr hfg) hprop hdiff
  have hh := mul_le_mul_of_nonneg_left h hg.le
  simpa only [mul_sub, ← mul_assoc, mul_div_cancel₀ f hg.ne'] using hh

section MeasurableLabels

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem entropyWith_gaussianCodebook_weighted_difference_le_of_precision
    (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N M S : Matrix ι ι ℝ)
    (hN : N.PosDef) (hM : M.PosDef) (hS : S.PosSemidef)
    {f g : ℝ} (hf : 0 < f) (hg : 0 < g) (hfg : f ≤ g)
    (hprop : g • (S + M)⁻¹ = f • (S + N)⁻¹) :
    f * entropyWith (gaussianCodebookKernel m N ∘ₘ μ) volume -
        g * entropyWith (gaussianCodebookKernel m M ∘ₘ μ) volume ≤
      f * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) (S + N)) volume -
        g * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) (S + M)) volume := by
  have hA : (S + N).PosDef := PosDef.posSemidef_add hS hN
  have hB : (S + M).PosDef := PosDef.posSemidef_add hS hM
  have hp : (S + M)⁻¹ = (f / g) • (S + N)⁻¹ := by
    have h := congrArg (fun Z ↦ g⁻¹ • Z) hprop
    simpa only [smul_smul, inv_mul_cancel₀ hg.ne', one_smul, div_eq_mul_inv, mul_comm] using h
  simp only [gaussianCodebookKernel_comp_eq_mixture]
  exact entropyWith_gaussianMixtureMeasure_weighted_difference_le_of_proportional
    (fun a ↦ μ.real {a}) (fun _ ↦ measureReal_nonneg) (sum_real_singleton_eq_one μ)
    m N M (S + N) (S + M) hN hB hf hg hfg (inv_proportional_smul hA hB hp).symm (by abel)

theorem entropyWith_gaussianCodebook_weighted_difference_le_of_proportional
    (μ : Measure α) [IsProbabilityMeasure μ]
    (m : α → EuclideanSpace ℝ ι) (N M A B : Matrix ι ι ℝ)
    (hN : N.PosDef) (hB : B.PosDef)
    {f g : ℝ} (hf : 0 < f) (hg : 0 < g) (hfg : f ≤ g)
    (hprop : A = (f / g) • B) (hdiff : M - N = B - A) :
    f * entropyWith (gaussianCodebookKernel m N ∘ₘ μ) volume -
        g * entropyWith (gaussianCodebookKernel m M ∘ₘ μ) volume ≤
      f * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) volume -
        g * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) volume := by
  simp only [gaussianCodebookKernel_comp_eq_mixture]
  exact entropyWith_gaussianMixtureMeasure_weighted_difference_le_of_proportional
    (fun a ↦ μ.real {a}) (fun _ ↦ measureReal_nonneg) (sum_real_singleton_eq_one μ)
    m N M A B hN hB hf hg hfg hprop hdiff

theorem integral_entropyWith_gaussianCodebook_weighted_difference_le_of_proportional
    {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (m : β → α → EuclideanSpace ℝ ι) (N M A B : Matrix ι ι ℝ)
    (hN : N.PosDef) (hB : B.PosDef)
    {f g : ℝ} (hf : 0 < f) (hg : 0 < g) (hfg : f ≤ g)
    (hprop : A = (f / g) • B) (hdiff : M - N = B - A) :
    f * (∫ b, entropyWith (gaussianCodebookKernel (m b) N ∘ₘ μ) volume ∂ν) -
        g * (∫ b, entropyWith (gaussianCodebookKernel (m b) M ∘ₘ μ) volume ∂ν) ≤
      f * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) volume -
        g * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) volume := by
  have h := integral_mono (μ := ν) Integrable.of_finite (integrable_const
    (f * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) volume -
      g * entropyWith (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) volume))
    (fun b ↦ entropyWith_gaussianCodebook_weighted_difference_le_of_proportional
      μ (m b) N M A B hN hB hf hg hfg hprop hdiff)
  simpa only [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const, probReal_univ, one_smul] using h

end MeasurableLabels

end CapacityAtlas.MeasureInformation
